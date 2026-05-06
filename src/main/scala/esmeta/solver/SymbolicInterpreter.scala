package esmeta.solver

import esmeta.cfg.*
import esmeta.es.util.Coverage.*
import esmeta.ir.{Func => _, *}
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.state.*
import esmeta.ty.ValueTy
import Formula.*, SymExpr.*
import scala.collection.mutable.{Map => MMap, Set => MSet, Queue}

class SymbolicInterpreter(
  entryFunc: Func,
  target: Branch,
  cond: Cond,
)(using cfg: CFG) {
  import SymbolicInterpreter.*

  private var env = MMap[Local, SymExpr]()
  // TODO: symbolic heap

  private var pendingReturn: Option[SymExpr] = None
  private var curFunc: Func = entryFunc

  // pre-populate env with structured symbolic IDs for entry params
  private val initEnv: Map[Local, SymExpr] = {
    val irParams = entryFunc.irFunc.params.flatMap { p =>
      p.lhs match
        case n if n.name == "this"      => Some(n -> Sym(SymId.This))
        case n if n.name == "NewTarget" => Some(n -> Sym(SymId.NewTarget))
        case _                          => None
    }
    val headArgs = entryFunc.head match
      case Some(h: BuiltinHead) =>
        h.params
          .collect { case p if p.kind != ParamKind.Variadic => p.name }
          .zipWithIndex
          .map((name, k) => Name(name) -> Sym(SymId.Arg(k)))
      case _ => Nil
    (irParams ++ headArgs :+ (Name(ARGS_STR) -> Sym(SymId.Args))).toMap
  }

  // functions we step into during symbolic execution
  private val targetFunc = cfg.funcOf.get(target)
  private val inCalleeTarget = targetFunc.exists(_ != entryFunc)
  private val stepInFuncs: Set[Func] =
    if (!inCalleeTarget) Set.empty
    else {
      val reached = MSet(targetFunc.get)
      val queue = Queue(targetFunc.get)
      while (queue.nonEmpty) {
        for {
          caller <- cfg.callerOf.getOrElse(queue.dequeue(), Set.empty)
          if caller.kind != FuncKind.InternalMeth &&
          reached.add(caller)
        } queue.enqueue(caller)
      }
      reached.toSet
    }

  // whitelist for pruning
  private val whitelist =
    if (!inCalleeTarget) entryFunc.reachingTo(target)
    else {
      val stepInCalls = entryFunc.nodes.flatMap {
        case c: Call =>
          c.callInst match
            case ICall(_, EClo(fname, _), _)
                if cfg.fnameMap.get(fname).exists(stepInFuncs.contains) =>
              Some(c)
            case _ => None
        case _ => None
      }
      if (stepInCalls.isEmpty) Set.empty[Node]
      else stepInCalls.flatMap(entryFunc.reachingTo)
    }
  private val calleeWhitelist =
    if (inCalleeTarget) targetFunc.get.reachingTo(target)
    else Set.empty[Node]

  // --- worklist types ---

  private case class CallFrame(
    func: Func,
    env: Map[Local, SymExpr],
    retId: Local,
    returnTo: Option[Node],
    visited: Set[Int],
  )

  private case class SymState(
    node: Node,
    cs: Goal,
    env: Map[Local, SymExpr],
    func: Func,
    stack: List[CallFrame],
    visited: Set[Int],
  )

  // --- results ---

  private val results = List.newBuilder[Goal]

  lazy val result: List[Goal] =
    if (whitelist.isEmpty && inCalleeTarget) Nil
    else {
      val init =
        SymState(
          entryFunc.entry,
          List(),
          initEnv,
          entryFunc,
          List(),
          Set(entryFunc.entry.id),
        )
      val wl = Queue(init)
      while (wl.nonEmpty) process(wl.dequeue(), wl)
      results.result()
    }

  // --- worklist processing ---

  private def process(st: SymState, wl: Queue[SymState]): Unit =
    env = MMap.from(st.env)
    curFunc = st.func
    pendingReturn = None

    def snapshot = env.toMap

    def enqueue(
      node: Node,
      cs: Goal,
      func: Func = curFunc,
      stack: List[CallFrame] = st.stack,
      visited: Set[Int] = st.visited,
    ): Unit =
      if (!visited(node.id) && reachable(node))
        wl.enqueue(SymState(node, cs, snapshot, func, stack, visited + node.id))

    def returnToCaller(cs: Goal): Unit =
      st.stack match
        case CallFrame(f, callerEnv, retId, returnTo, callerVisited) :: rest =>
          val rv = pendingReturn
          env = MMap.from(callerEnv)
          rv.foreach(v => env(retId) = v)
          curFunc = f
          returnTo.foreach(n => enqueue(n, cs, f, rest, callerVisited))
        case Nil => ()

    st.node match
      case block: Block =>
        eval(block)
        if (pendingReturn.isDefined) returnToCaller(st.cs)
        else
          block.next match
            case Some(n) => enqueue(n, st.cs)
            case None    => returnToCaller(st.cs)

      case branch: Branch if branch.id == target.id =>
        for (c <- getConstraints(branch.cond, cond.cond))
          results += (st.cs ++ c)

      case branch: Branch if branch.isFiltered =>
        for (n <- branch.thenNode.toList ++ branch.elseNode.toList)
          enqueue(n, st.cs)

      case branch: Branch =>
        eval(branch.cond) match
          case Lit(EBool(knownSide)) =>
            val nexts = if (knownSide) branch.thenNode else branch.elseNode
            nexts.foreach(n => enqueue(n, st.cs))
          case _ =>
            for {
              n <- branch.thenNode
              c <- getConstraints(branch.cond, true)
            } enqueue(n, st.cs ++ c)
            for {
              n <- branch.elseNode
              c <- getConstraints(branch.cond, false)
            } enqueue(n, st.cs ++ c)

      case call: Call =>
        val ret = call.lhs
        call.callInst match
          case ICall(_, EClo(fname, _), args) =>
            cfg.fnameMap.get(fname) match
              case Some(callee)
                  if stepInFuncs.contains(callee) &&
                  callee != curFunc &&
                  !st.stack.exists(_.func == callee) =>
                val argVals = args.map(eval)
                val frame =
                  CallFrame(curFunc, snapshot, ret, call.next, st.visited)
                val calleeEnv = MMap[Local, SymExpr]()
                for ((p, a) <- callee.irFunc.params.zip(argVals))
                  calleeEnv(p.lhs) = a
                wl.enqueue(
                  SymState(
                    callee.entry,
                    st.cs,
                    calleeEnv.toMap,
                    callee,
                    frame :: st.stack,
                    Set(callee.entry.id),
                  ),
                )
              case _ =>
                env(ret) = App(fname, args.map(eval))
                call.next.foreach(n => enqueue(n, st.cs))
          case ICall(_, ERef(Field(base, EStr(method))), args) =>
            env(ret) = App(method, eval(base) :: args.map(eval))
            call.next.foreach(n => enqueue(n, st.cs))
          case ISdoCall(_, base, op, args) =>
            env(ret) = App(op, eval(base) :: args.map(eval))
            call.next.foreach(n => enqueue(n, st.cs))
          case _ =>
            env.remove(ret)
            call.next.foreach(n => enqueue(n, st.cs))

  // --- block/instruction evaluation ---

  private def eval(block: Block): Unit =
    for (inst <- block.insts if pendingReturn.isEmpty) eval(inst)

  private def isBuiltinPrefix(inst: NormalInst): Boolean =
    (curFunc == entryFunc) && (inst match
      case ILet(lhs, _) if lhs == Name(ARGS_STR)         => true
      case IPop(Name(_), ERef(Name("ArgumentsList")), _) => true
      case IExpand(base, _) if base == Name(ARGS_STR)    => true
      case _                                             => false
    )

  private def eval(inst: NormalInst): Unit = inst match
    case inst if isBuiltinPrefix(inst) => ()
    case ILet(lhs, expr) =>
      env(lhs) = eval(expr)
    case IAssign(x: Local, expr) =>
      env(x) = eval(expr)
    case IAssign(Field(x: Local, EStr(key)), expr) =>
      val t = eval(expr)
      env.get(x) match
        case Some(SRecord(tn, fs)) => env(x) = SRecord(tn, fs + (key -> t))
        case _                     => ()
    case _: IAssign => () // global or dynamic-key assign
    case IExpand(base: Local, expr) =>
      eval(expr) match
        case Lit(EStr(field)) =>
          env.get(base) match
            case Some(SRecord(tn, fs)) if !fs.contains(field) =>
              env(base) = SRecord(tn, fs + (field -> Lit(EUndef())))
            case _ => ()
        case _ => ()
    case _: IExpand => () // non-local or dynamic-key expand
    case IDelete(base: Local, expr) =>
      val t = eval(expr)
      env.get(base) match
        case Some(SMap(es)) => env(base) = SMap(es.filterNot(_._1 == t))
        case _              => ()
    case _: IDelete => () // non-local or dynamic-key delete
    case IPush(elem, ERef(x: Local), front) =>
      val t = eval(elem)
      env.get(x) match
        case Some(SList(es)) =>
          env(x) = if (front) SList(t :: es) else SList(es :+ t)
        case _ => ()
    case _: IPush             => () // non-local list
    case IPop(x: Local, _, _) => env.remove(x)
    case IReturn(expr) =>
      pendingReturn = Some(eval(expr))
    case _ => ()

  // --- expression evaluation ---

  private def eval(expr: Expr): SymExpr = expr match
    case _: EParse | _: EGrammarSymbol | _: ESourceText => ??? // syntactic part
    case _: EYet => ??? // not implemented
    case EContains(list, elem) =>
      simplify(App("[ir:contains]", List(eval(list), eval(elem))))
    case ESubstring(base, from, to) =>
      val args = List(eval(base), eval(from)) ++ to.map(eval)
      simplify(App("[ir:substring]", args))
    case ETrim(base, isStarting) =>
      val op = if (isStarting) "[ir:trim-start]" else "[ir:trim-end]"
      simplify(App(op, List(eval(base))))
    case ERef(ref) => eval(ref)
    case EUnary(op, e) =>
      simplify(App(op, List(eval(e))))
    case EBinary(op, lhs, rhs) =>
      simplify(App(op, List(eval(lhs), eval(rhs))))
    case EVariadic(op, exprs) =>
      simplify(App(op, exprs.map(eval)))
    case EMathOp(mop, args) =>
      simplify(App(mop, args.map(eval)))
    case EConvert(cop, e) =>
      simplify(App(cop, List(eval(e))))
    case EExists(ref) =>
      ref match
        case Field(base, EStr(field)) =>
          eval(base) match
            case SRecord(_, fs) => Lit(EBool(fs.contains(field)))
            case SMap(es) =>
              val k = Lit(EStr(field))
              Lit(EBool(es.exists(_._1 == k)))
            case t => App("[ir:exists]", List(t, Lit(EStr(field))))
        case _ => Lit(EBool(true))
    case ETypeOf(e)     => TypeOf(eval(e))
    case _: EInstanceOf => ??? // syntactic part
    case ETypeCheck(e, ty) =>
      simplify(App(BOp.Eq, List(TypeOf(eval(e)), SType(ty.toValue))))
    case ESizeOf(e) =>
      eval(e) match
        case SList(elems) => Lit(EMath(BigDecimal(elems.size)))
        case t            => App("[ir:sizeof]", List(t))
    case _: EClo                     => ??? // opaque closure
    case _: ECont                    => ??? // opaque continuation
    case _: EDebug                   => ??? // debug
    case _: ERandom                  => ??? // non-deterministic
    case _: ESyntactic | _: ELexical => ??? // syntactic part
    case ERecord(tname, pairs) =>
      SRecord(tname, pairs.map((k, e) => k -> eval(e)).toMap)
    case EMap(_, pairs) => SMap(pairs.map((k, v) => (eval(k), eval(v))))
    case EList(exprs)   => SList(exprs.map(eval))
    case ECopy(obj)     => eval(obj)
    case EKeys(map, _) =>
      eval(map) match
        case SRecord(_, fs) => SList(fs.keys.map(k => Lit(EStr(k))).toList)
        case SMap(es)       => SList(es.map(_._1))
        case t              => App("[ir:keys]", List(t))
    case literal: LiteralExpr => Lit(literal)

  private def eval(ref: Ref): SymExpr = ref match
    case x: Local => env.getOrElse(x, Lit(EUndef()))
    case Global(name) =>
      val ty = ValueTy.fromTypeOf(name)
      if (!ty.isBottom) SType(ty) else App(name, Nil)
    case Field(base, EStr(name)) =>
      eval(base) match
        case SRecord(_, fs) if fs.contains(name) => fs(name)
        case SMap(es) =>
          val k = Lit(EStr(name))
          es.collectFirst { case (`k`, v) => v }
            .getOrElse(Proj(SMap(es), Lit(EStr(name))))
        case t => Proj(t, Lit(EStr(name)))
    case f @ Field(base, idx) =>
      (eval(base), eval(idx)) match
        case (SList(es), Lit(EMath(n)))
            if n.isValidInt && es.indices.contains(n.toInt) =>
          es(n.toInt)
        case (SMap(es), k) =>
          es.collectFirst { case (`k`, v) => v }
            .getOrElse(Proj(SMap(es), k))
        case (b, k) => Proj(b, k)

  private def getConstraints(expr: Expr, pos: Boolean): List[Goal] = expr match
    case EUnary(UOp.Not, inner) => getConstraints(inner, !pos)
    case ETypeCheck(base, ty) =>
      val f = FEq(TypeOf(eval(base)), SType(ty.toValue))
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
        case SRecord(_, fs) if fs.contains(field) =>
          if (pos) List(List()) else Nil
        case t =>
          val f = FExists(t, Lit(EStr(field)))
          List(List(if (pos) f else FNot(f)))
    case EContains(list, elem) =>
      (eval(list), eval(elem)) match
        case (SList(elems), t) =>
          if (pos) elems.map(e => List(FEq(t, e)))
          else List(elems.map(e => FNot(FEq(t, e))))
        case (Lit(EStr(s)), Lit(EStr(sub))) =>
          val result = s.contains(sub)
          if (result == pos) List(List()) else Nil
        case (l, r) =>
          val f = FEq(App("[ir:contains]", List(l, r)), Lit(EBool(true)))
          List(List(if (pos) f else FNot(f)))
    case ERef(ref) => List(List(FEq(eval(ref), Lit(EBool(pos)))))
    case _: EYet   => Nil
    case _         => ???

  // constant folding for literals
  private def simplify(t: SymExpr): SymExpr = t match
    case App(op: UOp, List(Lit(lit))) =>
      foldUOp(op, lit).getOrElse(t)
    case App(op: BOp, List(Lit(l), Lit(r))) =>
      foldBOp(op, l, r).getOrElse(t)
    case App(op: VOp, args) =>
      foldVOp(op, args).getOrElse(t)
    case App(op: MOp, args) =>
      foldMOp(op, args).getOrElse(t)
    case App(op: COp, List(Lit(lit))) =>
      foldCOp(op, lit).getOrElse(t)
    case App(_: COp, List(arg)) => arg
    case App("[ir:contains]", List(SList(es), t)) =>
      Lit(EBool(es.contains(t)))
    case App("[ir:contains]", List(Lit(EStr(s)), Lit(EStr(sub)))) =>
      Lit(EBool(s.contains(sub)))
    case App(
          "[ir:substring]",
          List(Lit(EStr(s)), Lit(EMath(f)), Lit(EMath(to))),
        ) =>
      val end = if (s.length < to.toInt) s.length else to.toInt
      Lit(EStr(s.substring(f.toInt, end)))
    case App("[ir:substring]", List(Lit(EStr(s)), Lit(EMath(f)))) =>
      Lit(EStr(s.substring(f.toInt)))
    case App("[ir:trim-start]", List(Lit(EStr(s)))) =>
      Lit(EStr(trimString(s, true, cfg.esParser)))
    case App("[ir:trim-end]", List(Lit(EStr(s)))) =>
      Lit(EStr(trimString(s, false, cfg.esParser)))
    case _ => t

  private def reachable(node: Node): Boolean =
    if (curFunc == entryFunc) whitelist(node)
    else if (inCalleeTarget && targetFunc.contains(curFunc))
      calleeWhitelist(node)
    else true
}

object SymbolicInterpreter {

  def apply(
    entryFunc: Func,
    target: Branch,
    cond: Cond,
  )(using CFG): List[Goal] =
    new SymbolicInterpreter(entryFunc, target, cond).result

  private def foldUOp(op: UOp, lit: LiteralExpr): Option[SymExpr] =
    import UOp.*
    (op, lit) match
      case (Abs, EMath(n)) => Some(Lit(EMath(n.abs)))
      case (Floor, EMath(n)) =>
        val f = if (n.isWhole) n else n - (n % 1) - (if (n < 0) 1 else 0)
        Some(Lit(EMath(f)))
      case (Neg, ENumber(n))     => Some(Lit(ENumber(-n)))
      case (Neg, EMath(n))       => Some(Lit(EMath(-n)))
      case (Neg, EInfinity(pos)) => Some(Lit(EInfinity(!pos)))
      case (Neg, EBigInt(n))     => Some(Lit(EBigInt(-n)))
      case (Not, EBool(b))       => Some(Lit(EBool(!b)))
      case (BNot, EMath(n))      => Some(Lit(EMath(~n.toInt)))
      case (BNot, ENumber(n))    => Some(Lit(ENumber(~n.toInt)))
      case (BNot, EBigInt(n))    => Some(Lit(EBigInt(~n)))
      case _                     => None

  private def foldBOp(
    op: BOp,
    l: LiteralExpr,
    r: LiteralExpr,
  ): Option[SymExpr] =
    import BOp.*
    (op, l, r) match
      case (Add, ENumber(a), ENumber(b)) => Some(Lit(ENumber(a + b)))
      case (Sub, ENumber(a), ENumber(b)) => Some(Lit(ENumber(a - b)))
      case (Mul, ENumber(a), ENumber(b)) => Some(Lit(ENumber(a * b)))
      case (Pow, ENumber(a), ENumber(b)) => Some(Lit(ENumber(math.pow(a, b))))
      case (Div, ENumber(a), ENumber(b)) => Some(Lit(ENumber(a / b)))
      case (Mod, ENumber(a), ENumber(b)) => Some(Lit(ENumber(a % b)))
      case (Lt, ENumber(a), ENumber(b))  => Some(Lit(EBool(a < b)))
      case (Add, EMath(a), EMath(b))     => Some(Lit(EMath(a + b)))
      case (Sub, EMath(a), EMath(b))     => Some(Lit(EMath(a - b)))
      case (Mul, EMath(a), EMath(b))     => Some(Lit(EMath(a * b)))
      case (Mod, EMath(a), EMath(b)) if b != BigDecimal(0) =>
        Some(Lit(EMath(a % b)))
      case (Pow, EMath(a), EMath(b)) if b.isValidInt && b >= 0 =>
        Some(Lit(EMath(a.pow(b.toInt))))
      case (BAnd, EMath(a), EMath(b)) =>
        Some(Lit(EMath(BigDecimal(a.toBigInt & b.toBigInt))))
      case (BOr, EMath(a), EMath(b)) =>
        Some(Lit(EMath(BigDecimal(a.toBigInt | b.toBigInt))))
      case (BXOr, EMath(a), EMath(b)) =>
        Some(Lit(EMath(BigDecimal(a.toBigInt ^ b.toBigInt))))
      case (LShift, EMath(a), EMath(b)) =>
        Some(Lit(EMath(BigDecimal(a.toBigInt << b.toInt))))
      case (RShift, EMath(a), EMath(b)) =>
        Some(Lit(EMath(BigDecimal(a.toBigInt >> b.toInt))))
      case (Lt, EMath(a), EMath(b))         => Some(Lit(EBool(a < b)))
      case (Add, EInfinity(true), EMath(_)) => Some(Lit(EInfinity(true)))
      case (Add, EMath(_), EInfinity(true)) => Some(Lit(EInfinity(true)))
      case (Add, EInfinity(true), EInfinity(true)) =>
        Some(Lit(EInfinity(true)))
      case (Add, EInfinity(false), EMath(_)) => Some(Lit(EInfinity(false)))
      case (Add, EMath(_), EInfinity(false)) => Some(Lit(EInfinity(false)))
      case (Add, EInfinity(false), EInfinity(false)) =>
        Some(Lit(EInfinity(false)))
      case (Sub, EInfinity(true), EMath(_)) => Some(Lit(EInfinity(true)))
      case (Sub, EInfinity(true), EInfinity(false)) =>
        Some(Lit(EInfinity(true)))
      case (Sub, EMath(_), EInfinity(true))  => Some(Lit(EInfinity(false)))
      case (Sub, EInfinity(false), EMath(_)) => Some(Lit(EInfinity(false)))
      case (Sub, EInfinity(false), EInfinity(true)) =>
        Some(Lit(EInfinity(false)))
      case (Sub, EMath(_), EInfinity(false)) => Some(Lit(EInfinity(true)))
      case (Eq, a, b)                        => Some(Lit(EBool(a == b)))
      case _                                 => None

  private def foldVOp(op: VOp, terms: List[SymExpr]): Option[SymExpr] =
    import VOp.*
    op match
      case Min =>
        if (terms.contains(Lit(EInfinity(false)))) Some(Lit(EInfinity(false)))
        else {
          val filtered = terms.filter(_ != Lit(EInfinity(true)))
          if (filtered.isEmpty) Some(Lit(EInfinity(true)))
          else {
            val nums = filtered.collect { case Lit(EMath(n)) => n }
            if (nums.size == filtered.size) Some(Lit(EMath(nums.min)))
            else None
          }
        }
      case Max =>
        if (terms.contains(Lit(EInfinity(true)))) Some(Lit(EInfinity(true)))
        else {
          val filtered = terms.filter(_ != Lit(EInfinity(false)))
          if (filtered.isEmpty) Some(Lit(EInfinity(false)))
          else {
            val nums = filtered.collect { case Lit(EMath(n)) => n }
            if (nums.size == filtered.size) Some(Lit(EMath(nums.max)))
            else None
          }
        }
      case Concat =>
        val strs = terms.collect {
          case Lit(EStr(s))      => s
          case Lit(ECodeUnit(c)) => c.toString
        }
        if (strs.size == terms.size) Some(Lit(EStr(strs.mkString)))
        else {
          val lists = terms.collect { case SList(es) => es }
          if (lists.size == terms.size) Some(SList(lists.flatten))
          else None
        }

  private def foldMOp(mop: MOp, terms: List[SymExpr]): Option[SymExpr] =
    import MOp.*
    val nums = terms.collect { case Lit(EMath(n)) => n.toDouble }
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
      r.map(v => Lit(EMath(v)))

  private def foldCOp(cop: COp, lit: LiteralExpr): Option[SymExpr] =
    import COp.*
    (cop, lit) match
      case (ToMath, EMath(n))     => Some(Lit(EMath(n)))
      case (ToMath, ENumber(d))   => Some(Lit(EMath(BigDecimal(d))))
      case (ToMath, EBigInt(n))   => Some(Lit(EMath(BigDecimal(n))))
      case (ToMath, ECodeUnit(c)) => Some(Lit(EMath(BigDecimal(c.toInt))))
      case (ToNumber, EMath(n))   => Some(Lit(ENumber(n.toDouble)))
      case (ToNumber, ENumber(d)) => Some(Lit(ENumber(d)))
      case (ToNumber, EInfinity(pos)) =>
        val v = if (pos) Double.PositiveInfinity else Double.NegativeInfinity
        Some(Lit(ENumber(v)))
      case (ToApproxNumber, EMath(n)) => Some(Lit(ENumber(n.toDouble)))
      case (ToBigInt, EMath(n))       => Some(Lit(EBigInt(n.toBigInt)))
      case (ToBigInt, EBigInt(n))     => Some(Lit(EBigInt(n)))
      case (ToCodeUnit, EMath(n))     => Some(Lit(ECodeUnit(n.toChar)))
      case (ToStr(_), EStr(s))        => Some(Lit(EStr(s)))
      case (ToStr(None), EMath(n)) =>
        Some(Lit(EStr(if (n.isWhole) n.toBigInt.toString else n.toString)))
      case (ToStr(None), EBigInt(n)) => Some(Lit(EStr(n.toString)))
      case (ToStr(None), ENumber(d)) =>
        if (d.isNaN) Some(Lit(EStr("NaN")))
        else if (d.isPosInfinity) Some(Lit(EStr("Infinity")))
        else if (d.isNegInfinity) Some(Lit(EStr("-Infinity")))
        else Some(Lit(EStr(d.toString)))
      case (ToStr(None), EInfinity(pos)) =>
        Some(Lit(EStr(if (pos) "Infinity" else "-Infinity")))
      case (ToStr(None), EBool(b)) => Some(Lit(EStr(b.toString)))
      case _                       => None
}
