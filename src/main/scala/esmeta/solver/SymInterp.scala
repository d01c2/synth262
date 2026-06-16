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
import scala.collection.mutable.{Set => MSet, Queue}

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
    if (targetFunc == entryFunc) Set(targetFunc)
    else {
      val reached = MSet(targetFunc)
      val queue = Queue(targetFunc)
      while (queue.nonEmpty)
        for {
          caller <- cfg.callerOf.getOrElse(queue.dequeue(), Set())
          if caller != entryFunc && reached.add(caller)
        } queue.enqueue(caller)
      reached.toSet
    }
  // candidate nodes
  inline def isCandidate(n: Node): Boolean = candidateNodes.contains(n)
  private lazy val candidateNodes: Set[Node] = for {
    func <- candidateFuncs + entryFunc
    node <- computeCandidateNodes(func)
  } yield node
  private def computeCandidateNodes(func: Func): Set[Node] = {
    if (func == targetFunc) func.reachingTo(target.branch) // direct reachables
    else {
      // reachables to call sites that can reach the target
      val callTargets = for {
        callTarget <- func.nodes.collect { case c: Call => c }
        calleeName <- callTarget.callInst match
          case ICall(_, EClo(fn, _), _) => Some(fn)
          case _                        => None
        callee <- cfg.fnameMap.get(calleeName)
        if isCandidate(callee)
      } yield callTarget
      callTargets.flatMap(func.reachingTo)
    }
  }

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
  // visited functions to avoid infinite exploration
  var funcs: Set[Func] = Set.empty
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
    if (!isCandidate(node)) return pop
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
          case ICall(_, fexpr, args) =>
            given callerNp: NodePoint[Call] = np.copy(node = call)
            val (retV, newSt) = (for {
              fv <- transfer.transfer(fexpr)
              st <- get
              given AbsState = st
              fty = fv.ty
              vs <- join(args.map(transfer.transfer(_, forArg = true)))
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
          case _ => ???
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
    funcs += func
  }

  // get the current configuration
  def getConfig: Config = Config(st, prev, funcs, loops)

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
      app :> s"Funcs: ${config.funcs.map(_.id).mkString(", ")}"
      app :> s"Loops: ${config.loops.map(_.id).mkString(", ")}"
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
}
type SymInterpRunner = (Func, Cond) => SymInterp
