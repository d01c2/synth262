package esmeta.solver

import esmeta.analyzer.tychecker.TyChecker
import esmeta.cfg.*
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{Func => _, *}
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.Appender.*
import esmeta.util.Appender.{*, given}
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Map => MMap, Queue}

class SymInterp(
  val tychecker: TyChecker,
  val entryFunc: Func,
  val target: Cond,
  val timeLimit: Option[Int] = None,
  val detail: Boolean = false,
) extends Solver {
  import tychecker.*, monad.*, SymTy.*, Result.*

  // start time
  val startTime: Long = System.currentTimeMillis

  // target function
  lazy val targetFunc: Func = cfg.funcOf(target.branch)

  // main entry point of symbolic execution
  lazy val result: Option[Config] = {
    if (!isCandidate(entryFunc)) None
    else
      try {
        initialize(entryFunc)
        while (true) step
        None
      } catch {
        case Found(config) => Some(config)
        case NotFound      => None
        case Timeout       => None
      }
  }

  // ---------------------------------------------------------------------------
  // symbolic execution state
  // ---------------------------------------------------------------------------
  // candidate functions
  inline def isCandidate(f: Func): Boolean = candidateFuncs.contains(f)
  private lazy val candidateFuncs: Set[Func] =
    SymInterp.candidateFuncs(entryFunc, targetFunc)(using cfg)
  // candidate nodes
  inline def isCandidate(n: Node): Boolean = candidateNodes.contains(n)
  private lazy val candidateNodes: Set[Node] =
    SymInterp.candidateNodes(entryFunc, target.branch)(using cfg)

  def timeout: Boolean = timeLimit.exists { limit =>
    val duration = System.currentTimeMillis - startTime
    duration >= limit.toLong * 1000L
  }

  // ---------------------------------------------------------------------------
  // symbolic execution configuration
  // ---------------------------------------------------------------------------
  // current node being executed
  var node: Node = entryFunc.builtinEntry.getOrElse(entryFunc.entry)
  // branch side will be taken
  var side: Boolean = true
  // current abstract state
  var st: AbsState = AbsState.Bot
  // previous states for backtracking
  var prev: Option[(Cond, Config)] = None
  // call stack
  var calls: List[Call] = Nil
  // visited functions to avoid infinite exploration
  var funcs: Set[Func] = Set(entryFunc)
  // visited loops to avoid infinite exploration
  var loops: Set[Branch] = Set.empty

  // symbolic execution of a node
  private def step: Unit = {
    // abort symbolic execution once the per-side time limit is exceeded
    if (timeout) throw Result.Timeout
    // -------------------------------------------------------------------------
    // XXX: remove
    // -------------------------------------------------------------------------
    log("=" * 80)
    log(s"Executing node ${node.name}:${if (side) "T" else "F"} $getConfig")
    log("-" * 80)
    log(node)
    // -------------------------------------------------------------------------
    given np: NodePoint[?] = NodePoint(cfg.funcOf(node), node, emptyView)
    if (!isCandidate(node) || st.isBottom) return pop
    node match
      case Block(_, insts, next) =>
        st = insts.zipWithIndex.foldLeft(st) {
          case (nextSt, _) if nextSt.isBottom => nextSt
          case (nextSt, (inst, idx)) => transfer.transfer(inst, idx)(nextSt)
        }
        next match
          case Some(next) => node = next
          case None       => pop
      case call: Call =>
        call.callInst match
          case ICall(_, fexpr @ EClo(f, Nil), args) =>
            val callee = cfg.fnameMap(f)
            if (isCandidate(callee) && !funcs.contains(callee)) {
              (for {
                vs <- join(args.map(transfer.transfer))
              } yield {
                given AbsState = st
                val params = callee.irFunc.params
                val vars: Set[Base] = st.locals.keySet.toSet
                val newLocals: Map[Local, AbsValue] = (for {
                  (param, arg) <- (params zip vs)
                } yield param.lhs -> arg.kill(vars, false)).toMap
                st = st.copy(locals = newLocals, constr = st.constr.onlySym)
              })(st)
              node = callee.entry
              funcs += callee
              calls ::= call
            } else doCall(call, EClo(f, Nil), args)
          case ICall(_, fexpr, args) => doCall(call, fexpr, args)
          case _                     => pop // TODO: handle other calls
      case branch: Branch if target.branch == branch =>
        // reached the target branch, check the constraint
        refine(branch, target.cond)
        if (check)
          // -------------------------------------------------------------------
          // XXX: remove
          // -------------------------------------------------------------------
          log("=" * 80)
          log(s"FOUND: $st")
          log("-" * 80)
          log(node)
          // -------------------------------------------------------------------
          throw Found(getConfig)
        else pop
      case branch @ Branch(_, kind, cond, _, thenNode, elseNode, _) =>
        // already visited this loop, skip it
        if (loops.contains(branch)) pop
        else {
          // first time visiting this loop, explore it
          if (branch.isLoop) loops += branch
          (thenNode, elseNode) match
            // TODO: pick a branch more smartly
            case (Some(tnode), _) if side  => push(branch, true); node = tnode
            case (_, Some(enode)) if !side => push(branch, false); node = enode
            case _                         => pop
        }
  }

  def doCall(
    call: Call,
    fexpr: Expr,
    args: List[Expr],
  )(using np: NodePoint[?]): Unit = {
    given callerNp: NodePoint[Call] = np.copy(node = call)
    val (retV, newSt) = (for {
      fv <- transfer.transfer(fexpr)
      st <- get
      given AbsState = st
      fty = fv.ty
      vs <- join(args.map(transfer.transfer))
    } yield {
      var retV = AbsValue.Bot
      fty.clo match
        case CloTopTy           => retV ⊔= AbsValue(AnyT)
        case CloArrowTy(_, ret) => retV ⊔= AbsValue(ret)
        case CloSetTy(names) =>
          for {
            fname <- names
            f <- cfg.fnameMap.get(fname)
            v = doCall(callerNp, f, st, vs)
          } retV ⊔= v
      fty.cont match
        case Inf => retV ⊔= AbsValue(AnyT)
        case Fin(fids) =>
          for {
            fid <- fty.cont.toIterable(stop = false)
            f <- cfg.funcMap.get(fid)
            v = doCall(callerNp, f, st, vs)
          } retV ⊔= v
      retV
    })(st)
    st = newSt.define(call.lhs, retV)
    call.next match
      case Some(next) => node = next
      case None       => pop
  }

  /** handle calls */
  def doCall(
    callerNp: NodePoint[Call],
    callee: Func,
    callerSt: AbsState,
    vs: List[AbsValue],
  ): AbsValue = {
    given AbsState = callerSt
    val call = callerNp.node
    val retTy = callee.retTy.ty.toValue
    (for {
      refiner <- transfer.manualRefiners.get(callee.name)
      v = refiner(callee, vs, retTy, callerSt)
      newV = instantiate(v, vs, callerNp, callerSt)
    } yield newV).getOrElse {
      val rp = ReturnPoint(callee, emptyView)
      val AbsRet(v) = getResult(rp)
      instantiate(v, vs, callerNp, callerSt) ⊓ AbsValue(retTy).lift
    }
  }

  /** instantiation of return value */
  def instantiate(
    value: AbsValue,
    vs: List[AbsValue],
    callerNp: NodePoint[Call],
    callerSt: AbsState,
  ): AbsValue =
    import DemandType.*
    given AbsState = callerSt
    val call = callerNp.node
    val map = vs.zipWithIndex.map {
      case (v, i) => i -> v
    }.toMap
    val newV = transfer.instantiate(call, value, map)
    if (inferTypeGuard && useSyntacticKill)
      newV.lift.killMutable(using callerNp)
    else if (inferTypeGuard) newV.lift
    else newV

  // ---------------------------------------------------------------------------
  // helper functions for configuration manipulation
  // ---------------------------------------------------------------------------
  // initialize the configuration for the given function
  private def initialize(func: Func): Unit = {
    node = func.builtinEntry.getOrElse(func.entry)
    st = func.head match {
      // built-in functions
      case Some(h: BuiltinHead) =>
        import ParamKind.*
        // environment for built-in functions
        var locals = Map[Local, AbsValue](
          NAME_THIS -> AbsValue(SThis),
          NAME_ARGS_LIST -> AbsValue(SArgs),
          NAME_NEW_TARGET -> AbsValue(SNewTarget),
        )
        val ps = h.params.zipWithIndex
        for {
          (p, i) <- ps
          sty = if (p.kind == Variadic) SArgs else SSym(i)
        } {
          locals += Name(p.name) -> AbsValue(sty)
        }
        // symbolic environment for built-in functions
        val symEnv = Map(
          SThis.sym -> ESValueT,
          SArgs.sym -> ListT(ESValueT),
          SNewTarget.sym -> ESValueT,
        ) ++ (for ((p, i) <- ps if p.kind != Variadic) yield {
          i -> ESValueT
        })
        AbsState(true, locals, symEnv, TypeConstr())
      case _ => AbsState.Bot
    }
  }

  // get the current configuration
  def getConfig: Config = Config(st, prev, funcs, calls, loops)

  // push the current config and refine it using the branch condition and side
  def push(branch: Branch, taken: Boolean)(using NodePoint[?]): Unit =
    prev = Some(Cond(branch, taken), getConfig)
    side = true
    refine(branch, taken)

  // pop the previous config and backtrack
  def pop: Unit = prev match
    case Some(Cond(branch, true), config) =>
      node = branch
      side = false
      st = config.state
      prev = config.prev
      funcs = config.funcs
      calls = config.calls
      loops = config.loops
    case Some(_, config) =>
      prev = config.prev
      pop
    case None => throw NotFound

  // refine the current abstract state based on the branch condition and side
  def refine(branch: Branch, taken: Boolean)(using NodePoint[?]): Unit = {
    import tychecker.RefinementTarget.*
    val expr = branch.cond
    (for { v <- transfer.transfer(expr); newSt <- get } yield {
      val target = Some(BranchTarget(branch, taken))
      st = transfer.refine(expr, v, BoolT(taken), target)(newSt)
    })(st)
  }

  // configuration of symbolic execution
  case class Config(
    state: AbsState,
    prev: Option[(Cond, Config)],
    funcs: Set[Func],
    calls: List[Call],
    loops: Set[Branch],
  ) {
    def path: List[Cond] = prev.map { (c, s) => c :: s.path }.getOrElse(Nil)
    override def toString: String = stringify(this)
  }

  given stateRule: Rule[Config] = (app, config) => {
    app.wrap {
      app :> s"AbsState: " >> config.state
      app :> s"Path: "
      val path = config.path
      if (path.nonEmpty) app.wrap {
        for (cond <- config.path.reverse)
          app :> s"${cond.branch.id}:${if (cond.cond) "T" else "F"}"
      }
      app :> s"Funcs: ${config.funcs.toList.map(_.id).sorted.mkString(", ")}"
      app :> s"Calls: ${config.calls.map(_.id).mkString(", ")}"
      app :> s"Loops: ${config.loops.toList.map(_.id).sorted.mkString(", ")}"
    }
  }

  // found valid path and formula
  enum Result extends Exception:
    case Found(state: Config)
    case NotFound
    case Timeout

  // logging
  def log(msg: => Any): Unit = if (detail) println(msg)
}

object SymInterp {
  def apply(
    cfg: CFG,
    timeLimit: Option[Int] = None,
    detail: Boolean = false,
  ): SymInterpRunner = {
    val tyChecker = TyChecker(cfg, silent = true)
    tyChecker.analyze
    new SymInterp(tyChecker, _, _, timeLimit = timeLimit, detail = detail)
  }

  /** BFS from `func` over the reverse call graph, mapping each reached function
    * to its distance (the number of call edges) from `func`. Traversal records
    * functions in `stopAt` but does not explore their callers.
    */
  def reachingDists(
    func: Func,
    stopAt: Set[Func] = Set.empty,
  )(using cfg: CFG): Map[Func, Int] = {
    val dist = MMap(func -> 0)
    val queue = Queue(func)
    while (queue.nonEmpty) {
      val cur = queue.dequeue()
      val nextDist = dist(cur) + 1
      if (!stopAt.contains(cur))
        for {
          caller <- cfg.callerOf.getOrElse(cur, Set.empty)
          if !dist.contains(caller)
        } {
          dist(caller) = nextDist
          queue.enqueue(caller)
        }
    }
    dist.toMap
  }

  /** built-in entries reaching the given branch, mapped to their distance (the
    * number of call edges from the entry to the branch's function)
    */
  def findEntries(branch: Branch)(using cfg: CFG): Map[Func, Int] =
    val func = cfg.funcOf(branch)
    if (func.isBuiltin) Map(func -> 0)
    else reachingDists(func).filter(_._1.isBuiltin)

  /** built-in entries reaching the given branch, ordered from the closest to
    * the farthest
    */
  def sortedEntries(branch: Branch)(using cfg: CFG): List[Func] =
    findEntries(branch).toList.sortBy(_._2).map(_._1)

  /** functions that may lie on a call path from `entry` to `target` (always
    * including `entry` itself)
    */
  def candidateFuncs(entry: Func, target: Func)(using cfg: CFG): Set[Func] =
    if (target == entry) Set(target)
    else reachingDists(target, stopAt = Set(entry)).keySet + entry

  /** nodes within candidate functions that can still reach the `target` branch
    */
  def candidateNodes(entry: Func, target: Branch)(using cfg: CFG): Set[Node] =
    val targetFunc = cfg.funcOf(target)
    val funcs = candidateFuncs(entry, targetFunc)
    for {
      func <- funcs + entry
      node <- computeCandidateNodes(func, funcs, targetFunc, target)
    } yield node

  private def computeCandidateNodes(
    func: Func,
    candidateFuncs: Set[Func],
    targetFunc: Func,
    target: Branch,
  )(using cfg: CFG): Set[Node] =
    if (func == targetFunc) func.reachingTo(target) // direct reachables
    else {
      // reachables to call sites that can reach the target
      val callTargets = for {
        callTarget <- func.nodes.collect { case c: Call => c }
        calleeName <- callTarget.callInst match
          case ICall(_, EClo(fn, _), _) => Some(fn)
          case _                        => None
        callee <- cfg.fnameMap.get(calleeName)
        if candidateFuncs.contains(callee)
      } yield callTarget
      callTargets.flatMap(func.reachingTo)
    }
}
type SymInterpRunner = (Func, Cond) => SymInterp
