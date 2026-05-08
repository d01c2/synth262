package esmeta.solver

import esmeta.cfg.*
import esmeta.es.util.Coverage.*
import esmeta.ir.{Func => _, *}
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.state.*
import esmeta.ty.ValueTy

import Formula.*, SymExpr.*

class SymbolicInterpreter(entryFunc: Func, target: Cond)(using cfg: CFG) {
  import SymbolicInterpreter.*
  private val Cond(branch, side) = target

  private var env = Map[Local, SymExpr]()
  // TODO: symbolic heap

  private var argCounter = 0 // FIXME: parameter setting branch flip case

  // backward reachable nodes from the target branch (for path pruning)
  private lazy val whitelist = entryFunc.reachingTo(branch)

  lazy val result: LazyList[Goal] =
    if (whitelist.isEmpty) LazyList()
    else {
      var stack = List[(Cond, Goal, Map[Local, SymExpr])]()

      // init symbolic environment from builtin entry parameters
      env = entryFunc.irFunc.params.flatMap { param =>
        val name = param.lhs
        if (name == NAME_THIS) Some(name -> SESym(Sym.This))
        else if (name == NAME_NEW_TARGET) Some(name -> SESym(Sym.NewTarget))
        else if (name == NAME_ARGS_LIST) Some(name -> SESym(Sym.ArgsList))
        else None
      }.toMap

      // path constraint
      def pc: Goal = stack.reverseIterator.flatMap(_._2).toList

      // try certain branch side and push constraints onto the stack
      def tryBranch(
        br: Branch,
        side: Boolean,
        feasible: Node => Boolean,
      ): Option[Node] =
        val savedEnv = env
        val nextNode = if (side) br.thenNode else br.elseNode
        val constraint =
          if (br.isFiltered) Some(List()) // skip extraction for filtered
          else getConstraint(br.cond, side)
        for {
          node <- nextNode.filter(feasible)
          cs <- constraint
        } yield { stack ::= (Cond(br, side), cs, savedEnv); node }

      def feasible(n: Node) =
        whitelist.contains(n) && // reachable to target
        !stack.exists(_._1.branch.id == n.id) // no re-entry into loops

      // cfg step with path pruning
      def step(node: Node): Option[Node] =
        node match
          case block: Block => eval(block); block.next.filter(feasible)
          case b: Branch =>
            eval(b.cond) match
              case SELit(EBool(v)) =>
                val nextNode = if (v) b.thenNode else b.elseNode
                nextNode.filter(feasible)
              case _ => // try true first and flip if not solvable
                tryBranch(b, true, feasible)
                  .orElse(tryBranch(b, false, feasible))
          case call: Call =>
            val ret = call.lhs
            call.callInst match
              case ICall(_, EClo(fname, _), args) =>
                env += (ret -> SEApp(fname, args.map(eval)))
              case ICall(_, ERef(Field(base, EStr(method))), args) =>
                env += (ret -> SEApp(method, eval(base) :: args.map(eval)))
              case ISdoCall(_, base, op, args) =>
                env += (ret -> SEApp(op, eval(base) :: args.map(eval)))
              case _ => env -= ret
            call.next.filter(feasible)

      // collect path constraints
      def collectGoal(from: Node): Option[Goal] = {
        var cur: Option[Node] = Some(from)
        var found: Option[Goal] = None
        try {
          while (cur.isDefined && found.isEmpty) {
            val node = cur.get
            node match
              case b: Branch if b.id == branch.id =>
                found = getConstraint(b.cond, side).map(pc ++ _)
                cur = None
              case _ => cur = step(node)
          }
        } catch {
          case _: NotImplementedError | _: MatchError => ()
        }
        found
      }

      // pop the stack and try the else-side of the most recent then-branch
      def backtrack(): Option[Node] = {
        var found: Option[Node] = None
        while (stack.nonEmpty && found.isEmpty) {
          val (Cond(br, tried), _, savedEnv) = stack.head
          stack = stack.tail
          if (tried) {
            env = savedEnv
            found = tryBranch(br, false, feasible)
          }
        }
        found
      }

      def emit(from: Node): LazyList[Goal] =
        def next(): LazyList[Goal] = backtrack() match
          case Some(n) => emit(n)
          case None    => LazyList()
        collectGoal(from) match
          case Some(goal) => goal #:: next()
          case None       => next()

      emit(entryFunc.entry)
    }

  // --- block/instruction evaluation ---

  private def eval(block: Block): Unit = for (inst <- block.insts) eval(inst)

  private def eval(inst: NormalInst): Unit = inst match
    case ILet(lhs, expr)         => env += (lhs -> eval(expr))
    case IAssign(x: Local, expr) => env += (x -> eval(expr))
    case IAssign(Field(x: Local, EStr(key)), expr) =>
      val t = eval(expr)
      env.get(x) match
        case Some(SERecord(tn, fs)) =>
          env += (x -> SERecord(tn, fs + (key -> t)))
        case _ => ()
    case _: IAssign => () // global or dynamic-key assign
    case IExpand(base: Local, expr) =>
      eval(expr) match
        case SELit(EStr(field)) =>
          env.get(base) match
            case Some(SERecord(tn, fs)) if !fs.contains(field) =>
              env += (base -> SERecord(tn, fs + (field -> SELit(EUndef()))))
            case _ => ()
        case _ => ()
    case _: IExpand => () // non-local or dynamic-key expand
    case IDelete(base: Local, expr) =>
      val t = eval(expr)
      env.get(base) match
        case Some(SEMap(es)) => env += (base -> SEMap(es.filterNot(_._1 == t)))
        case _               => ()
    case _: IDelete => () // non-local or dynamic-key delete
    case IPush(elem, ERef(x: Local), front) =>
      val t = eval(elem)
      env.get(x) match
        case Some(SEList(es)) =>
          env += (x -> (if (front) SEList(t :: es) else SEList(es :+ t)))
        case _ => ()
    case _: IPush => () // non-local list
    case IPop(lhs, ERef(x: Local), _) =>
      env.get(x) match
        case Some(SESym(Sym.ArgsList)) =>
          env += (lhs -> SESym(Sym.Arg(argCounter)))
          argCounter += 1
        case Some(SEList(es)) if es.nonEmpty =>
          env += (lhs -> es.head)
          env += (x -> SEList(es.tail))
        case _ => env -= lhs
    case _: IPop => env -= inst.asInstanceOf[IPop].lhs
    case _       => ()

  // --- expression evaluation ---

  private def eval(expr: Expr): SymExpr = expr match
    case _: EParse | _: EGrammarSymbol | _: ESourceText => ??? // syntactic
    case _: EYet => ??? // not implemented
    case EContains(list, elem) =>
      simplify(SEApp("[ir:contains]", List(eval(list), eval(elem))))
    case ESubstring(base, from, to) =>
      val args = List(eval(base), eval(from)) ++ to.map(eval)
      simplify(SEApp("[ir:substring]", args))
    case ETrim(base, isStarting) =>
      val op = if (isStarting) "[ir:trim-start]" else "[ir:trim-end]"
      simplify(SEApp(op, List(eval(base))))
    case ERef(ref) => eval(ref)
    case EUnary(op, e) =>
      simplify(SEApp(op, List(eval(e))))
    case EBinary(op, lhs, rhs) =>
      simplify(SEApp(op, List(eval(lhs), eval(rhs))))
    case EVariadic(op, exprs) =>
      simplify(SEApp(op, exprs.map(eval)))
    case EMathOp(mop, args) =>
      simplify(SEApp(mop, args.map(eval)))
    case EConvert(cop, e) =>
      simplify(SEApp(cop, List(eval(e))))
    case EExists(ref) =>
      ref match
        case Field(base, EStr(field)) =>
          eval(base) match
            case SERecord(_, fs) => SELit(EBool(fs.contains(field)))
            case SEMap(es) =>
              val k = SELit(EStr(field))
              SELit(EBool(es.exists(_._1 == k)))
            case t => SEApp("[ir:exists]", List(t, SELit(EStr(field))))
        case _ => SELit(EBool(true))
    case ETypeOf(e)     => SETypeOf(eval(e))
    case _: EInstanceOf => ??? // syntactic part
    case ETypeCheck(e, ty) =>
      simplify(SEApp(BOp.Eq, List(SETypeOf(eval(e)), SEType(ty.toValue))))
    case ESizeOf(e) =>
      eval(e) match
        case SEList(elems) => SELit(EMath(BigDecimal(elems.size)))
        case t             => SEApp("[ir:sizeof]", List(t))
    case _: EClo                     => ??? // opaque closure
    case _: ECont                    => ??? // opaque continuation
    case _: EDebug                   => ??? // debug
    case _: ERandom                  => ??? // non-deterministic
    case _: ESyntactic | _: ELexical => ??? // syntactic part
    case ERecord(tname, pairs) =>
      SERecord(tname, pairs.map((k, e) => k -> eval(e)).toMap)
    case EMap(_, pairs) => SEMap(pairs.map((k, v) => (eval(k), eval(v))))
    case EList(exprs)   => SEList(exprs.map(eval))
    case ECopy(obj)     => eval(obj)
    case EKeys(map, _) =>
      eval(map) match
        case SERecord(_, fs) => SEList(fs.keys.map(k => SELit(EStr(k))).toList)
        case SEMap(es)       => SEList(es.map(_._1))
        case t               => SEApp("[ir:keys]", List(t))
    case literal: LiteralExpr => SELit(literal)

  private def eval(ref: Ref): SymExpr = ref match
    case x: Local => env.getOrElse(x, SELit(EUndef()))
    case Global(name) =>
      val ty = ValueTy.fromTypeOf(name)
      if (!ty.isBottom) SEType(ty) else SEApp(name, List())
    case Field(base, EStr(name)) =>
      eval(base) match
        case SERecord(_, fs) if fs.contains(name) => fs(name)
        case SEMap(es) =>
          es.collectFirst {
            case (SELit(EStr(`name`)), v) => v
          }.getOrElse(SEProj(SEMap(es), SELit(EStr(name))))
        case t => SEProj(t, SELit(EStr(name)))
    case f @ Field(base, idx) =>
      (eval(base), eval(idx)) match
        case (SEList(es), SELit(EMath(n)))
            if n.isValidInt && es.indices.contains(n.toInt) =>
          es(n.toInt)
        case (SEMap(es), k) =>
          es.collectFirst { case (`k`, v) => v }
            .getOrElse(SEProj(SEMap(es), k))
        case (b, k) => SEProj(b, k)

  // --- constraint extraction ---

  private def getConstraint(expr: Expr, pos: Boolean): Option[Goal] =
    expr match
      case EUnary(UOp.Not, inner) => getConstraint(inner, !pos)
      case ETypeCheck(base, ty) =>
        val f = FEq(SETypeOf(eval(base)), SEType(ty.toValue))
        Some(List(if (pos) f else FNot(f)))
      case EBinary(BOp.Eq | BOp.Equal, lhs, rhs) =>
        (lhs, rhs) match
          case (_, EBool(b)) => getConstraint(lhs, if (pos) b else !b)
          case (EBool(b), _) => getConstraint(rhs, if (pos) b else !b)
          case _ =>
            val f = FEq(eval(lhs), eval(rhs))
            Some(List(if (pos) f else FNot(f)))
      case EBinary(BOp.Lt, lhs, rhs) =>
        val f = FLt(eval(lhs), eval(rhs))
        Some(List(if (pos) f else FNot(f)))
      case EBinary(BOp.And, lhs, rhs) if pos =>
        for {
          l <- getConstraint(lhs, true)
          r <- getConstraint(rhs, true)
        } yield l ++ r
      case EBinary(BOp.Or, lhs, rhs) if !pos =>
        for {
          l <- getConstraint(lhs, false)
          r <- getConstraint(rhs, false)
        } yield l ++ r
      case EBinary(BOp.And, lhs, rhs) =>
        getConstraint(lhs, false).orElse(getConstraint(rhs, false))
      case EBinary(BOp.Or, lhs, rhs) =>
        getConstraint(lhs, true).orElse(getConstraint(rhs, true))
      case EExists(Field(base, EStr(field))) =>
        eval(base) match
          case SERecord(_, fs) if fs.contains(field) =>
            if (pos) Some(List()) else None
          case t =>
            val f = FExists(t, SELit(EStr(field)))
            Some(List(if (pos) f else FNot(f)))
      case EContains(list, elem) =>
        (eval(list), eval(elem)) match
          case (SEList(elems), t) =>
            if (pos) elems.headOption.map(e => List(FEq(t, e)))
            else Some(elems.map(e => FNot(FEq(t, e))))
          case (SELit(EStr(s)), SELit(EStr(sub))) =>
            if (s.contains(sub) == pos) Some(List()) else None
          case (l, r) =>
            val f = FEq(SEApp("[ir:contains]", List(l, r)), SELit(EBool(true)))
            Some(List(if (pos) f else FNot(f)))
      case ERef(ref) => Some(List(FEq(eval(ref), SELit(EBool(pos)))))
      case _: EYet   => None
      case _         => ???

  // constant folding for literals
  private def simplify(t: SymExpr): SymExpr = t match
    case SEApp(op: UOp, List(SELit(lit))) =>
      foldUOp(op, lit).getOrElse(t)
    case SEApp(op: BOp, List(SELit(l), SELit(r))) =>
      foldBOp(op, l, r).getOrElse(t)
    case SEApp(op: VOp, args) =>
      foldVOp(op, args).getOrElse(t)
    case SEApp(op: MOp, args) =>
      foldMOp(op, args).getOrElse(t)
    case SEApp(op: COp, List(SELit(lit))) =>
      foldCOp(op, lit).getOrElse(t)
    case SEApp(_: COp, List(arg)) => arg
    case SEApp("[ir:contains]", List(SEList(es), t)) =>
      SELit(EBool(es.contains(t)))
    case SEApp("[ir:contains]", List(SELit(EStr(s)), SELit(EStr(sub)))) =>
      SELit(EBool(s.contains(sub)))
    case SEApp(
          "[ir:substring]",
          List(SELit(EStr(s)), SELit(EMath(f)), SELit(EMath(to))),
        ) =>
      val end = if (s.length < to.toInt) s.length else to.toInt
      SELit(EStr(s.substring(f.toInt, end)))
    case SEApp("[ir:substring]", List(SELit(EStr(s)), SELit(EMath(f)))) =>
      SELit(EStr(s.substring(f.toInt)))
    case SEApp("[ir:trim-start]", List(SELit(EStr(s)))) =>
      SELit(EStr(trimString(s, true, cfg.esParser)))
    case SEApp("[ir:trim-end]", List(SELit(EStr(s)))) =>
      SELit(EStr(trimString(s, false, cfg.esParser)))
    case _ => t
}

object SymbolicInterpreter {

  def apply(entryFunc: Func, target: Cond)(using CFG): LazyList[Goal] =
    new SymbolicInterpreter(entryFunc, target).result

  private def foldUOp(op: UOp, lit: LiteralExpr): Option[SymExpr] =
    import UOp.*
    (op, lit) match
      case (Abs, EMath(n)) => Some(SELit(EMath(n.abs)))
      case (Floor, EMath(n)) =>
        val f = if (n.isWhole) n else n - (n % 1) - (if (n < 0) 1 else 0)
        Some(SELit(EMath(f)))
      case (Neg, ENumber(n))     => Some(SELit(ENumber(-n)))
      case (Neg, EMath(n))       => Some(SELit(EMath(-n)))
      case (Neg, EInfinity(pos)) => Some(SELit(EInfinity(!pos)))
      case (Neg, EBigInt(n))     => Some(SELit(EBigInt(-n)))
      case (Not, EBool(b))       => Some(SELit(EBool(!b)))
      case (BNot, EMath(n))      => Some(SELit(EMath(~n.toInt)))
      case (BNot, ENumber(n))    => Some(SELit(ENumber(~n.toInt)))
      case (BNot, EBigInt(n))    => Some(SELit(EBigInt(~n)))
      case _                     => None

  private def foldBOp(
    op: BOp,
    l: LiteralExpr,
    r: LiteralExpr,
  ): Option[SymExpr] =
    import BOp.*
    (op, l, r) match
      case (Add, ENumber(a), ENumber(b)) => Some(SELit(ENumber(a + b)))
      case (Sub, ENumber(a), ENumber(b)) => Some(SELit(ENumber(a - b)))
      case (Mul, ENumber(a), ENumber(b)) => Some(SELit(ENumber(a * b)))
      case (Pow, ENumber(a), ENumber(b)) => Some(SELit(ENumber(math.pow(a, b))))
      case (Div, ENumber(a), ENumber(b)) => Some(SELit(ENumber(a / b)))
      case (Mod, ENumber(a), ENumber(b)) => Some(SELit(ENumber(a % b)))
      case (Lt, ENumber(a), ENumber(b))  => Some(SELit(EBool(a < b)))
      case (Add, EMath(a), EMath(b))     => Some(SELit(EMath(a + b)))
      case (Sub, EMath(a), EMath(b))     => Some(SELit(EMath(a - b)))
      case (Mul, EMath(a), EMath(b))     => Some(SELit(EMath(a * b)))
      case (Mod, EMath(a), EMath(b)) if b != BigDecimal(0) =>
        Some(SELit(EMath(a % b)))
      case (Pow, EMath(a), EMath(b)) if b.isValidInt && b >= 0 =>
        Some(SELit(EMath(a.pow(b.toInt))))
      case (BAnd, EMath(a), EMath(b)) =>
        Some(SELit(EMath(BigDecimal(a.toBigInt & b.toBigInt))))
      case (BOr, EMath(a), EMath(b)) =>
        Some(SELit(EMath(BigDecimal(a.toBigInt | b.toBigInt))))
      case (BXOr, EMath(a), EMath(b)) =>
        Some(SELit(EMath(BigDecimal(a.toBigInt ^ b.toBigInt))))
      case (LShift, EMath(a), EMath(b)) =>
        Some(SELit(EMath(BigDecimal(a.toBigInt << b.toInt))))
      case (RShift, EMath(a), EMath(b)) =>
        Some(SELit(EMath(BigDecimal(a.toBigInt >> b.toInt))))
      case (Lt, EMath(a), EMath(b))         => Some(SELit(EBool(a < b)))
      case (Add, EInfinity(true), EMath(_)) => Some(SELit(EInfinity(true)))
      case (Add, EMath(_), EInfinity(true)) => Some(SELit(EInfinity(true)))
      case (Add, EInfinity(true), EInfinity(true)) =>
        Some(SELit(EInfinity(true)))
      case (Add, EInfinity(false), EMath(_)) => Some(SELit(EInfinity(false)))
      case (Add, EMath(_), EInfinity(false)) => Some(SELit(EInfinity(false)))
      case (Add, EInfinity(false), EInfinity(false)) =>
        Some(SELit(EInfinity(false)))
      case (Sub, EInfinity(true), EMath(_)) => Some(SELit(EInfinity(true)))
      case (Sub, EInfinity(true), EInfinity(false)) =>
        Some(SELit(EInfinity(true)))
      case (Sub, EMath(_), EInfinity(true))  => Some(SELit(EInfinity(false)))
      case (Sub, EInfinity(false), EMath(_)) => Some(SELit(EInfinity(false)))
      case (Sub, EInfinity(false), EInfinity(true)) =>
        Some(SELit(EInfinity(false)))
      case (Sub, EMath(_), EInfinity(false)) => Some(SELit(EInfinity(true)))
      case (Eq, a, b)                        => Some(SELit(EBool(a == b)))
      case _                                 => None

  private def foldVOp(op: VOp, terms: List[SymExpr]): Option[SymExpr] =
    import VOp.*
    op match
      case Min =>
        if (terms.contains(SELit(EInfinity(false))))
          Some(SELit(EInfinity(false)))
        else {
          val filtered = terms.filter(_ != SELit(EInfinity(true)))
          if (filtered.isEmpty) Some(SELit(EInfinity(true)))
          else {
            val nums = filtered.collect { case SELit(EMath(n)) => n }
            if (nums.size == filtered.size) Some(SELit(EMath(nums.min)))
            else None
          }
        }
      case Max =>
        if (terms.contains(SELit(EInfinity(true)))) Some(SELit(EInfinity(true)))
        else {
          val filtered = terms.filter(_ != SELit(EInfinity(false)))
          if (filtered.isEmpty) Some(SELit(EInfinity(false)))
          else {
            val nums = filtered.collect { case SELit(EMath(n)) => n }
            if (nums.size == filtered.size) Some(SELit(EMath(nums.max)))
            else None
          }
        }
      case Concat =>
        val strs = terms.collect {
          case SELit(EStr(s))      => s
          case SELit(ECodeUnit(c)) => c.toString
        }
        if (strs.size == terms.size) Some(SELit(EStr(strs.mkString)))
        else {
          val lists = terms.collect { case SEList(es) => es }
          if (lists.size == terms.size) Some(SEList(lists.flatten))
          else None
        }

  private def foldMOp(mop: MOp, terms: List[SymExpr]): Option[SymExpr] =
    import MOp.*
    val nums = terms.collect { case SELit(EMath(n)) => n.toDouble }
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
      r.map(v => SELit(EMath(v)))

  private def foldCOp(cop: COp, lit: LiteralExpr): Option[SymExpr] =
    import COp.*
    (cop, lit) match
      case (ToMath, EMath(n))     => Some(SELit(EMath(n)))
      case (ToMath, ENumber(d))   => Some(SELit(EMath(BigDecimal(d))))
      case (ToMath, EBigInt(n))   => Some(SELit(EMath(BigDecimal(n))))
      case (ToMath, ECodeUnit(c)) => Some(SELit(EMath(BigDecimal(c.toInt))))
      case (ToNumber, EMath(n))   => Some(SELit(ENumber(n.toDouble)))
      case (ToNumber, ENumber(d)) => Some(SELit(ENumber(d)))
      case (ToNumber, EInfinity(pos)) =>
        val v = if (pos) Double.PositiveInfinity else Double.NegativeInfinity
        Some(SELit(ENumber(v)))
      case (ToApproxNumber, EMath(n)) => Some(SELit(ENumber(n.toDouble)))
      case (ToBigInt, EMath(n))       => Some(SELit(EBigInt(n.toBigInt)))
      case (ToBigInt, EBigInt(n))     => Some(SELit(EBigInt(n)))
      case (ToCodeUnit, EMath(n))     => Some(SELit(ECodeUnit(n.toChar)))
      case (ToStr(_), EStr(s))        => Some(SELit(EStr(s)))
      case (ToStr(None), EMath(n)) =>
        Some(SELit(EStr(if (n.isWhole) n.toBigInt.toString else n.toString)))
      case (ToStr(None), EBigInt(n)) => Some(SELit(EStr(n.toString)))
      case (ToStr(None), ENumber(d)) =>
        if (d.isNaN) Some(SELit(EStr("NaN")))
        else if (d.isPosInfinity) Some(SELit(EStr("Infinity")))
        else if (d.isNegInfinity) Some(SELit(EStr("-Infinity")))
        else Some(SELit(EStr(d.toString)))
      case (ToStr(None), EInfinity(pos)) =>
        Some(SELit(EStr(if (pos) "Infinity" else "-Infinity")))
      case (ToStr(None), EBool(b)) => Some(SELit(EStr(b.toString)))
      case _                       => None
}
