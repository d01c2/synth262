package esmeta.solver

import esmeta.cfg.*
import esmeta.es.util.Coverage.*
import esmeta.ir.{Func => _, *}
import esmeta.ty.ValueTy
import Formula.*, Term.*
import scala.collection.mutable.{Map => MMap}

// Forward Symbolic Interpreter: walks a path, producing DNF goals
class SymbolicInterpreter(func: Func, path: Path, cond: Cond) {
  import SymbolicInterpreter.*

  private val env = MMap[Local, Term]()
  private val fields = MMap[(Local, String), Term]()

  private var goals: List[Goal] = List(List())

  /** walk the path, accumulating constraints into goals */
  lazy val result: List[Goal] =
    for ((node, idx) <- path.zipWithIndex) eval(node, idx)
    goals

  /** evaluation for nodes */
  private def eval(node: Node, idx: Int): Unit = node match
    case block: Block                        => eval(block)
    case call: Call                          => eval(call)
    case branch: Branch if branch.isFiltered => ()
    case branch: Branch =>
      val pos =
        if (branch.id == cond.branch.id) cond.cond // target branch
        else branch.thenNode.exists(_.id == path(idx + 1).id) // follow path
      goals = for {
        prev <- goals
        cond <- getConstraints(branch.cond, pos)
      } yield prev ++ cond

  private def bind(x: Local, expr: Expr): Unit =
    try env(x) = eval(expr)
    catch case _: Throwable => env.remove(x)
    fields.filterInPlace((k, _) => k._1 != x)

  /** evaluation for blocks */
  private def eval(block: Block): Unit =
    for (inst <- block.insts)
      inst match
        case ILet(lhs, expr)         => bind(lhs, expr)
        case IAssign(x: Local, expr) => bind(x, expr)
        case IAssign(Field(x: Local, EStr(key)), expr) =>
          try fields((x, key)) = eval(expr)
          catch case _: Throwable => fields.remove((x, key))
        // TODO: global assign, computed-key field assign [heap]
        case _: IAssign => ()
        // TODO: record field addition, deletion, list push [heap]
        case _: IExpand | _: IDelete | _: IPush => ()
        // argument pop handled by entryParams in Solve
        case IPop(Name(_), ERef(Name("ArgumentsList")), _) => ()
        case IPop(x: Local, _, _)                          => env.remove(x)
        // TODO: return value propagation [interproc]
        case _: IReturn => ()
        // no symbolic effect: IExpr, IAssert, IPrint, INop
        case _ => ()

  /** evaluation for calls */
  private def eval(call: Call): Unit =
    val ret = call.lhs
    call.callInst match
      case ICall(_, EClo(fname, _), args) =>
        env(ret) = TApp(fname, args.map(eval))
      case ICall(_, ERef(Field(base, EStr(method))), args) =>
        env(ret) = TApp(method, eval(base) :: args.map(eval))
      case _ => env.remove(ret)

  /** evaluation for expressions */
  private def eval(expr: Expr): Term = expr match
    case _: EParse         => ??? // not modelable
    case _: EGrammarSymbol => ??? // not modelable
    case _: ESourceText    => ??? // not modelable
    case _: EYet           => ??? // not modelable
    case _: EContains      => ??? // TODO [term]
    case _: ESubstring     => ??? // TODO [term]
    case _: ETrim          => ??? // TODO [term]
    case ERef(ref)         => eval(ref)
    case EUnary(op, e) =>
      eval(e) match
        case TLit(lit) => fold(op, lit).getOrElse(TUOp(op, TLit(lit)))
        case t         => TUOp(op, t)
    case EBinary(op, lhs, rhs) =>
      (eval(lhs), eval(rhs)) match
        case (TLit(l), TLit(r)) =>
          fold(op, l, r).getOrElse(TBOp(op, TLit(l), TLit(r)))
        case (l, r) => TBOp(op, l, r)
    case EVariadic(op, exprs) =>
      val ts = exprs.map(eval)
      fold(op, ts).getOrElse(TVOp(op, ts))
    case _: EMathOp => ??? // TODO [term]
    case EConvert(cop, e) =>
      val t = eval(e)
      t match
        case TLit(lit) => fold(cop, lit).getOrElse(t)
        case _         => t
    case _: EExists        => ??? // condition-only: handled in getConstraints
    case ETypeOf(e)        => TTypeOf(eval(e))
    case _: EInstanceOf    => ??? // condition-only: handled in getConstraints
    case ETypeCheck(e, ty) => TBOp(BOp.Eq, TTypeOf(eval(e)), TType(ty.toValue))
    case ESizeOf(e) =>
      eval(e) match
        case TList(elems) => TLit(EMath(BigDecimal(elems.size)))
        case t            => TSizeOf(t)
    case _: EClo              => ??? // opaque: used as call targets
    case _: ECont             => ??? // opaque: used as call targets
    case _: EDebug            => ??? // not modelable
    case _: ERandom           => ??? // not modelable
    case _: ESyntactic        => ??? // not modelable
    case _: ELexical          => ??? // not modelable
    case _: ERecord           => ??? // TODO [heap]
    case _: EMap              => ??? // TODO [heap]
    case EList(exprs)         => TList(exprs.map(eval))
    case _: ECopy             => ??? // TODO [heap]
    case _: EKeys             => ??? // TODO [heap]
    case literal: LiteralExpr => TLit(literal)

  /** evaluation for references */
  private def eval(ref: Ref): Term = ref match
    case x: Local =>
      env.getOrElse(x, TVar(x.toString))
    case Global(name) =>
      val ty = ValueTy.fromTypeOf(name)
      if (!ty.isBottom) TType(ty) else TVar(name)
    case Field(x: Local, EStr(k)) if fields.contains((x, k)) =>
      fields((x, k))
    case Field(base, EStr(name)) => TField(eval(base), name)
    case f @ Field(_, _)         => TVar(f.toString) // opaque computed field

  /** get constraints from branch condition as DNF */
  // NOTE: forks into multiple goals at disjunction to preserve DNF form
  private def getConstraints(expr: Expr, pos: Boolean): List[Goal] = expr match
    case EUnary(UOp.Not, inner) => getConstraints(inner, !pos)
    case ETypeCheck(base, ty) =>
      val f = FEq(TTypeOf(eval(base)), TType(ty.toValue))
      List(List(if (pos) f else FNot(f)))
    case EBinary(BOp.Eq | BOp.Equal, lhs, rhs) =>
      (lhs, rhs) match
        case (_, EBool(b)) => getConstraints(lhs, if (pos) b else !b)
        case (EBool(b), _) => getConstraints(rhs, if (pos) b else !b)
        case _ =>
          val f = FEq(eval(lhs), eval(rhs))
          List(List(if (pos) f else FNot(f)))
    case EBinary(BOp.Lt, lhs, rhs) =>
      val f = FLt(eval(lhs), eval(rhs))
      List(List(if (pos) f else FNot(f)))
    case EBinary(BOp.And, lhs, rhs) if pos =>
      for {
        l <- getConstraints(lhs, true)
        r <- getConstraints(rhs, true)
      } yield l ++ r
    case EBinary(BOp.Or, lhs, rhs) if !pos =>
      for {
        l <- getConstraints(lhs, false)
        r <- getConstraints(rhs, false)
      } yield l ++ r
    case EBinary(BOp.And, lhs, rhs) =>
      getConstraints(lhs, false) ++ getConstraints(rhs, false)
    case EBinary(BOp.Or, lhs, rhs) =>
      getConstraints(lhs, true) ++ getConstraints(rhs, true)
    case EExists(Field(base, EStr(field))) =>
      val f = FExists(eval(base), field)
      List(List(if (pos) f else FNot(f)))
    case EContains(list, elem) =>
      (eval(list), eval(elem)) match
        case (TList(elems), t) =>
          if (pos) elems.map(e => List(FEq(t, e)))
          else List(elems.map(e => FNot(FEq(t, e))))
        case (TLit(EStr(s)), TLit(EStr(sub))) =>
          val result = s.contains(sub)
          if (result == pos) List(List()) else Nil
        case (l, r) =>
          val f = FEq(TApp("Contains", List(l, r)), TLit(EBool(true)))
          List(List(if (pos) f else FNot(f)))
    case ERef(ref) => List(List(FEq(eval(ref), TLit(EBool(pos)))))
    case _: EYet   => Nil
    case _         => ???
}

object SymbolicInterpreter {

  /** diagnostic: track unsupported expressions */
  val failedExprs = MMap[String, Int]()

  def apply(func: Func, path: Path, cond: Cond): List[Goal] =
    try { new SymbolicInterpreter(func, path, cond).result }
    catch {
      case e: Throwable =>
        // record the failing expression
        val key =
          // extract the failing method from stack trace
          val frame = e.getStackTrace.find(f =>
            f.getClassName.contains("SymbolicInterpreter") &&
            !f.getMethodName.contains("apply"),
          )
          val loc =
            frame.fold("")(f => s"${f.getMethodName}:${f.getLineNumber}")
          s"${e.getClass.getSimpleName}($loc)"
        failedExprs.synchronized {
          failedExprs(key) = failedExprs.getOrElse(key, 0) + 1
        }
        Nil
    }

  /** constant folding for binary operations */
  private def fold(op: BOp, l: LiteralExpr, r: LiteralExpr): Option[Term] =
    import BOp.*
    (op, l, r) match
      case (Add, EMath(a), EMath(b)) => Some(TLit(EMath(a + b)))
      case (Sub, EMath(a), EMath(b)) => Some(TLit(EMath(a - b)))
      case (Mul, EMath(a), EMath(b)) => Some(TLit(EMath(a * b)))
      case (Mod, EMath(a), EMath(b)) if b != BigDecimal(0) =>
        Some(TLit(EMath(a % b)))
      case (Lt, EMath(a), EMath(b)) => Some(TLit(EBool(a < b)))
      case (Eq, a, b)               => Some(TLit(EBool(a == b)))
      case _                        => None

  /** constant folding for unary operations */
  private def fold(op: UOp, lit: LiteralExpr): Option[Term] =
    import UOp.*
    (op, lit) match
      case (Neg, EMath(n)) => Some(TLit(EMath(-n)))
      case (Not, EBool(b)) => Some(TLit(EBool(!b)))
      case _               => None

  /** constant folding for variadic operations */
  private def fold(op: VOp, terms: List[Term]): Option[Term] =
    import VOp.*
    op match
      case Concat =>
        val strs = terms.collect { case TLit(EStr(s)) => s }
        if (strs.size == terms.size) Some(TLit(EStr(strs.mkString)))
        else {
          val lists = terms.collect { case TList(es) => es }
          if (lists.size == terms.size) Some(TList(lists.flatten))
          else None
        }
      case Min =>
        val nums = terms.collect { case TLit(EMath(n)) => n }
        if (nums.size == terms.size && nums.nonEmpty)
          Some(TLit(EMath(nums.min)))
        else None
      case Max =>
        val nums = terms.collect { case TLit(EMath(n)) => n }
        if (nums.size == terms.size && nums.nonEmpty)
          Some(TLit(EMath(nums.max)))
        else None

  /** constant folding for type conversions */
  private def fold(cop: COp, lit: LiteralExpr): Option[Term] =
    import COp.*
    (cop, lit) match
      // to math
      case (ToMath, EMath(n))     => Some(TLit(EMath(n)))
      case (ToMath, ENumber(d))   => Some(TLit(EMath(BigDecimal(d))))
      case (ToMath, EBigInt(n))   => Some(TLit(EMath(BigDecimal(n))))
      case (ToMath, ECodeUnit(c)) => Some(TLit(EMath(BigDecimal(c.toInt))))
      // to number
      case (ToNumber, EMath(n))   => Some(TLit(ENumber(n.toDouble)))
      case (ToNumber, ENumber(d)) => Some(TLit(ENumber(d)))
      case (ToNumber, EInfinity(pos)) =>
        Some(
          TLit(
            ENumber(
              if (pos) Double.PositiveInfinity else Double.NegativeInfinity,
            ),
          ),
        )
      case (ToApproxNumber, EMath(n)) => Some(TLit(ENumber(n.toDouble)))
      // to bigint
      case (ToBigInt, EMath(n))   => Some(TLit(EBigInt(n.toBigInt)))
      case (ToBigInt, EBigInt(n)) => Some(TLit(EBigInt(n)))
      // to code unit
      case (ToCodeUnit, EMath(n)) => Some(TLit(ECodeUnit(n.toChar)))
      // to string
      case (ToStr(_), EStr(s)) => Some(TLit(EStr(s)))
      case (ToStr(None), EMath(n)) =>
        Some(TLit(EStr(if (n.isWhole) n.toBigInt.toString else n.toString)))
      case (ToStr(None), EBigInt(n)) => Some(TLit(EStr(n.toString)))
      case (ToStr(None), ENumber(d)) =>
        if (d.isNaN) Some(TLit(EStr("NaN")))
        else if (d.isPosInfinity) Some(TLit(EStr("Infinity")))
        else if (d.isNegInfinity) Some(TLit(EStr("-Infinity")))
        else Some(TLit(EStr(d.toString)))
      case (ToStr(None), EInfinity(pos)) =>
        Some(TLit(EStr(if (pos) "Infinity" else "-Infinity")))
      case (ToStr(None), EBool(b)) => Some(TLit(EStr(b.toString)))
      case _                       => None
}
