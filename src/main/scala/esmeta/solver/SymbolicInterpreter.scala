package esmeta.solver

import esmeta.cfg.*
import esmeta.es.util.Coverage.*
import esmeta.ir.{Func => _, *}
import esmeta.state.*
import esmeta.ty.ValueTy
import Formula.*, Term.*
import scala.collection.mutable.{Map => MMap}

class SymbolicInterpreter(cfg: CFG, func: Func, path: Path, cond: Cond) {
  import SymbolicInterpreter.*

  private val state = MMap[Local, Term]()
  private val fields = MMap[(Local, String), Term]()

  private var goals: List[Goal] = List(List())

  lazy val result: List[Goal] =
    for ((node, idx) <- path.zipWithIndex) eval(node, idx)
    goals

  private def eval(node: Node, idx: Int): Unit = node match
    case block: Block                        => eval(block)
    case call: Call                          => eval(call)
    case branch: Branch if branch.isFiltered => ()
    case branch: Branch =>
      val pos = // lookup the side taken at the branch
        if (branch.id == cond.branch.id) cond.cond
        else branch.thenNode.exists(_.id == path(idx + 1).id)
      goals = for {
        prev <- goals
        cs <- getConstraints(branch.cond, pos)
      } yield prev ++ cs

  private def eval(block: Block): Unit = block.insts.foreach(eval)

  // check if normalInst is builtin prefix
  private def isBuiltinPrefix(inst: NormalInst): Boolean = inst match
    case ILet(lhs, _) if lhs == Name(ARGS_STR)         => true
    case IPop(Name(_), ERef(Name("ArgumentsList")), _) => true
    case IExpand(base, _) if base == Name(ARGS_STR)    => true
    case _                                             => false

  private def eval(inst: NormalInst): Unit = inst match
    case inst if isBuiltinPrefix(inst) => ()
    case ILet(lhs, expr) =>
      state(lhs) = eval(expr)
      fields.keys.filter(_._1 == lhs).foreach(fields.remove)
    case IAssign(x: Local, expr) =>
      state(x) = eval(expr)
      fields.keys.filter(_._1 == x).foreach(fields.remove)
    case IAssign(Field(x: Local, EStr(key)), expr) =>
      val t = eval(expr)
      state.get(x) match
        case Some(TRecord(tn, fs)) => state(x) = TRecord(tn, fs + (key -> t))
        case _                     => fields((x, key)) = t
    case _: IAssign => () // global or dynamic-key assign
    case IExpand(base: Local, expr) =>
      eval(expr) match
        case TLit(EStr(field)) =>
          state.get(base) match
            case Some(TRecord(tn, fs)) if !fs.contains(field) =>
              state(base) = TRecord(tn, fs + (field -> TLit(EUndef())))
            case _ => ()
        case _ => ()
    case _: IExpand => () // non-local or dynamic-key expand
    case IDelete(base: Local, expr) =>
      val t = eval(expr)
      state.get(base) match
        case Some(TMap(es)) => state(base) = TMap(es.filterNot(_._1 == t))
        case _              => ()
    case _: IDelete => () // non-local or dynamic-key delete
    case IPush(elem, ERef(x: Local), front) =>
      val t = eval(elem)
      state.get(x) match
        case Some(TList(es)) =>
          state(x) = if (front) TList(t :: es) else TList(es :+ t)
        case _ => ()
    case _: IPush             => () // non-local list
    case IPop(x: Local, _, _) => state.remove(x)
    case _: IReturn           => () // TODO: support inter-procedural
    case _                    => ()

  // TODO: support inter-procedural
  private def eval(call: Call): Unit =
    val ret = call.lhs
    call.callInst match
      case ICall(_, EClo(fname, _), args) =>
        state(ret) = TApp(fname, args.map(eval))
      case ICall(_, ERef(Field(base, EStr(method))), args) =>
        state(ret) = TApp(method, eval(base) :: args.map(eval))
      case ISdoCall(_, base, op, args) =>
        state(ret) = TApp(op, eval(base) :: args.map(eval))
      case _ => state.remove(ret)

  private def eval(expr: Expr): Term = expr match
    case _: EParse         => ??? // syntactic part
    case _: EGrammarSymbol => ??? // syntactic part
    case _: ESourceText    => ??? // syntactic part
    case _: EYet           => ??? // not implemented
    case EContains(list, elem) =>
      simplify(TApp("[ir:contains]", List(eval(list), eval(elem))))
    case ESubstring(base, from, to) =>
      val args = List(eval(base), eval(from)) ++ to.map(eval)
      simplify(TApp("[ir:substring]", args))
    case ETrim(base, isStarting) =>
      val op = if (isStarting) "[ir:trim-start]" else "[ir:trim-end]"
      simplify(TApp(op, List(eval(base))))
    case ERef(ref) => eval(ref)
    case EUnary(op, e) =>
      simplify(TApp(op, List(eval(e))))
    case EBinary(op, lhs, rhs) =>
      simplify(TApp(op, List(eval(lhs), eval(rhs))))
    case EVariadic(op, exprs) =>
      simplify(TApp(op, exprs.map(eval)))
    case EMathOp(mop, args) =>
      simplify(TApp(mop, args.map(eval)))
    case EConvert(cop, e) =>
      simplify(TApp(cop, List(eval(e))))
    case EExists(ref) =>
      ref match
        case Field(base, EStr(field)) =>
          eval(base) match
            case TRecord(_, fs) => TLit(EBool(fs.contains(field)))
            case TMap(es) =>
              val k = TLit(EStr(field))
              TLit(EBool(es.exists(_._1 == k)))
            case t => TApp("[ir:exists]", List(t, TLit(EStr(field))))
        case _ => TLit(EBool(true))
    case ETypeOf(e)     => TTypeOf(eval(e))
    case _: EInstanceOf => ??? // syntactic part
    case ETypeCheck(e, ty) =>
      simplify(TApp(BOp.Eq, List(TTypeOf(eval(e)), TType(ty.toValue))))
    case ESizeOf(e) =>
      eval(e) match
        case TList(elems) => TLit(EMath(BigDecimal(elems.size)))
        case t            => TApp("[ir:sizeof]", List(t))
    case _: EClo       => ??? // opaque closure
    case _: ECont      => ??? // opaque continuation
    case _: EDebug     => ??? // debug
    case _: ERandom    => ??? // non-deterministic
    case _: ESyntactic => ??? // syntactic part
    case _: ELexical   => ??? // syntactic part
    case ERecord(tname, pairs) =>
      TRecord(tname, pairs.map((k, e) => k -> eval(e)).toMap)
    case EMap(_, pairs) => TMap(pairs.map((k, v) => (eval(k), eval(v))))
    case EList(exprs)   => TList(exprs.map(eval))
    case ECopy(obj)     => eval(obj)
    case EKeys(map, _) =>
      eval(map) match
        case TRecord(_, fs) => TList(fs.keys.map(k => TLit(EStr(k))).toList)
        case TMap(es)       => TList(es.map(_._1))
        case t              => TApp("[ir:keys]", List(t))
    case literal: LiteralExpr => TLit(literal)

  private def eval(ref: Ref): Term = ref match
    case x: Local =>
      state.getOrElse(x, TVar(x.toString))
    case Global(name) =>
      val ty = ValueTy.fromTypeOf(name)
      if (!ty.isBottom) TType(ty) else TVar(name)
    case Field(x: Local, EStr(k)) if fields.contains((x, k)) =>
      fields((x, k))
    case Field(base, EStr(name)) =>
      eval(base) match
        case TRecord(_, fs) if fs.contains(name) => fs(name)
        case TMap(es) =>
          val k = TLit(EStr(name))
          es.collectFirst { case (`k`, v) => v }
            .getOrElse(TField(TMap(es), name))
        case t => TField(t, name)
    case f @ Field(base, idx) =>
      (eval(base), eval(idx)) match
        case (TList(es), TLit(EMath(n)))
            if n.isValidInt && es.indices.contains(n.toInt) =>
          es(n.toInt)
        case (TMap(es), k) =>
          es.collectFirst { case (`k`, v) => v }.getOrElse(TVar(f.toString))
        case _ => TVar(f.toString)

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
      eval(base) match
        case TRecord(_, fs) if fs.contains(field) =>
          if (pos) List(List()) else Nil
        case t =>
          val f = FExists(t, field)
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
          val f = FEq(TApp("[ir:contains]", List(l, r)), TLit(EBool(true)))
          List(List(if (pos) f else FNot(f)))
    case ERef(ref) => List(List(FEq(eval(ref), TLit(EBool(pos)))))
    case _: EYet   => Nil
    case _         => ???

  // constant folding for literals
  private def simplify(t: Term): Term = t match
    case TApp(op: UOp, List(TLit(lit))) =>
      foldUOp(op, lit).getOrElse(t)
    case TApp(op: BOp, List(TLit(l), TLit(r))) =>
      foldBOp(op, l, r).getOrElse(t)
    case TApp(op: VOp, args) =>
      foldVOp(op, args).getOrElse(t)
    case TApp(op: MOp, args) =>
      foldMOp(op, args).getOrElse(t)
    case TApp(op: COp, List(TLit(lit))) =>
      foldCOp(op, lit).getOrElse(t)
    case TApp(_: COp, List(arg)) => arg
    case TApp("[ir:contains]", List(TList(es), t)) =>
      TLit(EBool(es.contains(t)))
    case TApp("[ir:contains]", List(TLit(EStr(s)), TLit(EStr(sub)))) =>
      TLit(EBool(s.contains(sub)))
    case TApp(
          "[ir:substring]",
          List(TLit(EStr(s)), TLit(EMath(f)), TLit(EMath(to))),
        ) =>
      val end = if (s.length < to.toInt) s.length else to.toInt
      TLit(EStr(s.substring(f.toInt, end)))
    case TApp("[ir:substring]", List(TLit(EStr(s)), TLit(EMath(f)))) =>
      TLit(EStr(s.substring(f.toInt)))
    case TApp("[ir:trim-start]", List(TLit(EStr(s)))) =>
      TLit(EStr(trimString(s, true, cfg.esParser)))
    case TApp("[ir:trim-end]", List(TLit(EStr(s)))) =>
      TLit(EStr(trimString(s, false, cfg.esParser)))
    case _ => t
}

object SymbolicInterpreter {

  def apply(cfg: CFG, func: Func, path: Path, cond: Cond): List[Goal] =
    try { new SymbolicInterpreter(cfg, func, path, cond).result }
    catch { case _: Throwable => Nil }

  private def foldUOp(op: UOp, lit: LiteralExpr): Option[Term] =
    import UOp.*
    (op, lit) match
      case (Abs, EMath(n)) => Some(TLit(EMath(n.abs)))
      case (Floor, EMath(n)) =>
        val f = if (n.isWhole) n else n - (n % 1) - (if (n < 0) 1 else 0)
        Some(TLit(EMath(f)))
      case (Neg, ENumber(n))     => Some(TLit(ENumber(-n)))
      case (Neg, EMath(n))       => Some(TLit(EMath(-n)))
      case (Neg, EInfinity(pos)) => Some(TLit(EInfinity(!pos)))
      case (Neg, EBigInt(n))     => Some(TLit(EBigInt(-n)))
      case (Not, EBool(b))       => Some(TLit(EBool(!b)))
      case (BNot, EMath(n))      => Some(TLit(EMath(~n.toInt)))
      case (BNot, ENumber(n))    => Some(TLit(ENumber(~n.toInt)))
      case (BNot, EBigInt(n))    => Some(TLit(EBigInt(~n)))
      case _                     => None

  private def foldBOp(op: BOp, l: LiteralExpr, r: LiteralExpr): Option[Term] =
    import BOp.*
    (op, l, r) match
      case (Add, ENumber(a), ENumber(b)) => Some(TLit(ENumber(a + b)))
      case (Sub, ENumber(a), ENumber(b)) => Some(TLit(ENumber(a - b)))
      case (Mul, ENumber(a), ENumber(b)) => Some(TLit(ENumber(a * b)))
      case (Pow, ENumber(a), ENumber(b)) => Some(TLit(ENumber(math.pow(a, b))))
      case (Div, ENumber(a), ENumber(b)) => Some(TLit(ENumber(a / b)))
      case (Mod, ENumber(a), ENumber(b)) => Some(TLit(ENumber(a % b)))
      case (Lt, ENumber(a), ENumber(b))  => Some(TLit(EBool(a < b)))
      case (Add, EMath(a), EMath(b))     => Some(TLit(EMath(a + b)))
      case (Sub, EMath(a), EMath(b))     => Some(TLit(EMath(a - b)))
      case (Mul, EMath(a), EMath(b))     => Some(TLit(EMath(a * b)))
      case (Mod, EMath(a), EMath(b)) if b != BigDecimal(0) =>
        Some(TLit(EMath(a % b)))
      case (Pow, EMath(a), EMath(b)) if b.isValidInt && b >= 0 =>
        Some(TLit(EMath(a.pow(b.toInt))))
      case (BAnd, EMath(a), EMath(b)) =>
        Some(TLit(EMath(BigDecimal(a.toBigInt & b.toBigInt))))
      case (BOr, EMath(a), EMath(b)) =>
        Some(TLit(EMath(BigDecimal(a.toBigInt | b.toBigInt))))
      case (BXOr, EMath(a), EMath(b)) =>
        Some(TLit(EMath(BigDecimal(a.toBigInt ^ b.toBigInt))))
      case (LShift, EMath(a), EMath(b)) =>
        Some(TLit(EMath(BigDecimal(a.toBigInt << b.toInt))))
      case (RShift, EMath(a), EMath(b)) =>
        Some(TLit(EMath(BigDecimal(a.toBigInt >> b.toInt))))
      case (Lt, EMath(a), EMath(b))         => Some(TLit(EBool(a < b)))
      case (Add, EInfinity(true), EMath(_)) => Some(TLit(EInfinity(true)))
      case (Add, EMath(_), EInfinity(true)) => Some(TLit(EInfinity(true)))
      case (Add, EInfinity(true), EInfinity(true)) =>
        Some(TLit(EInfinity(true)))
      case (Add, EInfinity(false), EMath(_)) => Some(TLit(EInfinity(false)))
      case (Add, EMath(_), EInfinity(false)) => Some(TLit(EInfinity(false)))
      case (Add, EInfinity(false), EInfinity(false)) =>
        Some(TLit(EInfinity(false)))
      case (Sub, EInfinity(true), EMath(_)) => Some(TLit(EInfinity(true)))
      case (Sub, EInfinity(true), EInfinity(false)) =>
        Some(TLit(EInfinity(true)))
      case (Sub, EMath(_), EInfinity(true))  => Some(TLit(EInfinity(false)))
      case (Sub, EInfinity(false), EMath(_)) => Some(TLit(EInfinity(false)))
      case (Sub, EInfinity(false), EInfinity(true)) =>
        Some(TLit(EInfinity(false)))
      case (Sub, EMath(_), EInfinity(false)) => Some(TLit(EInfinity(true)))
      case (Eq, a, b)                        => Some(TLit(EBool(a == b)))
      case _                                 => None

  private def foldVOp(op: VOp, terms: List[Term]): Option[Term] =
    import VOp.*
    op match
      case Min =>
        if (terms.contains(TLit(EInfinity(false)))) Some(TLit(EInfinity(false)))
        else {
          val filtered = terms.filter(_ != TLit(EInfinity(true)))
          if (filtered.isEmpty) Some(TLit(EInfinity(true)))
          else {
            val nums = filtered.collect { case TLit(EMath(n)) => n }
            if (nums.size == filtered.size) Some(TLit(EMath(nums.min)))
            else None
          }
        }
      case Max =>
        if (terms.contains(TLit(EInfinity(true)))) Some(TLit(EInfinity(true)))
        else {
          val filtered = terms.filter(_ != TLit(EInfinity(false)))
          if (filtered.isEmpty) Some(TLit(EInfinity(false)))
          else {
            val nums = filtered.collect { case TLit(EMath(n)) => n }
            if (nums.size == filtered.size) Some(TLit(EMath(nums.max)))
            else None
          }
        }
      case Concat =>
        val strs = terms.collect {
          case TLit(EStr(s))      => s
          case TLit(ECodeUnit(c)) => c.toString
        }
        if (strs.size == terms.size) Some(TLit(EStr(strs.mkString)))
        else {
          val lists = terms.collect { case TList(es) => es }
          if (lists.size == terms.size) Some(TList(lists.flatten))
          else None
        }

  private def foldMOp(mop: MOp, terms: List[Term]): Option[Term] =
    import MOp.*
    val nums = terms.collect { case TLit(EMath(n)) => n.toDouble }
    if (nums.size != terms.size) None
    else
      val r: Option[Double] = (mop, nums) match
        case (Expm1, List(a))    => Some(math.expm1(a))
        case (Log10, List(a))    => Some(math.log10(a))
        case (Log2, List(a))     => Some(math.log(a) / math.log(2))
        case (Cos, List(a))      => Some(math.cos(a))
        case (Cbrt, List(a))     => Some(math.cbrt(a))
        case (Exp, List(a))      => Some(math.exp(a))
        case (Cosh, List(a))     => Some(math.cosh(a))
        case (Sinh, List(a))     => Some(math.sinh(a))
        case (Tanh, List(a))     => Some(math.tanh(a))
        case (Acos, List(a))     => Some(math.acos(a))
        case (Asin, List(a))     => Some(math.asin(a))
        case (Atan2, List(a, b)) => Some(math.atan2(a, b))
        case (Atan, List(a))     => Some(math.atan(a))
        case (Log1p, List(a))    => Some(math.log1p(a))
        case (Log, List(a))      => Some(math.log(a))
        case (Sin, List(a))      => Some(math.sin(a))
        case (Sqrt, List(a))     => Some(math.sqrt(a))
        case (Tan, List(a))      => Some(math.tan(a))
        case _                   => None // Acosh, Asinh, Atanh not supported
      r.map(v => TLit(EMath(v)))

  private def foldCOp(cop: COp, lit: LiteralExpr): Option[Term] =
    import COp.*
    (cop, lit) match
      case (ToMath, EMath(n))     => Some(TLit(EMath(n)))
      case (ToMath, ENumber(d))   => Some(TLit(EMath(BigDecimal(d))))
      case (ToMath, EBigInt(n))   => Some(TLit(EMath(BigDecimal(n))))
      case (ToMath, ECodeUnit(c)) => Some(TLit(EMath(BigDecimal(c.toInt))))
      case (ToNumber, EMath(n))   => Some(TLit(ENumber(n.toDouble)))
      case (ToNumber, ENumber(d)) => Some(TLit(ENumber(d)))
      case (ToNumber, EInfinity(pos)) =>
        val v = if (pos) Double.PositiveInfinity else Double.NegativeInfinity
        Some(TLit(ENumber(v)))
      case (ToApproxNumber, EMath(n)) => Some(TLit(ENumber(n.toDouble)))
      case (ToBigInt, EMath(n))       => Some(TLit(EBigInt(n.toBigInt)))
      case (ToBigInt, EBigInt(n))     => Some(TLit(EBigInt(n)))
      case (ToCodeUnit, EMath(n))     => Some(TLit(ECodeUnit(n.toChar)))
      case (ToStr(_), EStr(s))        => Some(TLit(EStr(s)))
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
