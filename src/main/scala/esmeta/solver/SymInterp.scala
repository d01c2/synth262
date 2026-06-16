package esmeta.solver

import esmeta.cfg.*
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{Func => _, *}
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.Appender.*
import esmeta.util.Appender.{*, given}
import esmeta.util.BaseUtils.*

class SymInterp(
  cfg: CFG,
  entryFunc: Func,
  target: Cond,
) {
  import SymInterp.*, Result.*

  lazy val result: Option[State] = execute

  // ---------------------------------------------------------------------------
  // symbolic execution state
  // ---------------------------------------------------------------------------
  // current node being executed
  var node: Node = entryFunc.entry
  // environment mapping local variables to symbolic expressions
  var env: Map[Local, SymExpr] = Map.empty
  // symbolic environment mapping symbols to their shapes
  var symEnv: SymEnv = SymEnv.empty
  // previous states for backtracking
  var prev: Option[(Cond, State)] = None
  // visited functions to avoid infinite exploration
  var funcs: Set[Func] = Set.empty
  // visited loops to avoid infinite exploration
  var loops: Set[Branch] = Set.empty

  // target
  val targetFunc: Func = cfg.funcOf(target.branch)

  // ---------------------------------------------------------------------------
  // helper functions for symbolic execution
  // ---------------------------------------------------------------------------
  // main symbolic execution loop
  private def execute: Option[State] = {
    if (!isCandidate(entryFunc)) return None
    enterFunc(entryFunc)
    try {
      while (true) step
      None
    } catch {
      case Found(state) => Some(state)
      case NotFound     => None
    }
  }

  // symbolic execution of a node
  private def step: Unit = {
    // -------------------------------------------------------------------------
    // XXX: remove
    // -------------------------------------------------------------------------
    println("=" * 80)
    println(s"Executing node ${node.name}: $getState")
    println("-" * 80)
    println(node)
    // -------------------------------------------------------------------------
    node match
      case block: Block =>
        for (inst <- block.insts) eval(inst)
        block.next match
          case Some(next) => node = next
          case None       => throw NotFound
      case call: Call                                => ???
      case branch: Branch if target.branch == branch =>
        // reached the target branch, check the constraint
        symEnv = Solver.add(symEnv, eval(branch.cond), target.cond)
        if (Solver.check(symEnv)) throw Found(getState)
        else pop
      case branch: Branch =>
        // already visited this loop, skip it
        if (loops.contains(branch)) pop
        else {
          // first time visiting this loop, explore it
          if (branch.isLoop) loops += branch
          val sexpr = eval(branch.cond)
          (branch.thenNode, branch.elseNode) match
            // TODO: pick a branch more smartly
            case (Some(tnode), _) => push(branch, sexpr, true); node = tnode
            case (_, Some(enode)) => push(branch, sexpr, false); node = enode
            case _                => pop
        }
  }

  // symbolic execution of a normal instruction
  private def eval(inst: NormalInst): Unit = inst match
    case ILet(lhs, expr) => env += lhs -> eval(expr)
    case INop(_)         =>
    case _               => ???

  // symbolic execution of an expression
  private def eval(expr: Expr): SymExpr = expr match
    case EParse(code, rule)                       => ???
    case EGrammarSymbol(name, params)             => ???
    case ESourceText(expr)                        => ???
    case EYet(msg)                                => ???
    case EContains(list, elem)                    => ???
    case ESubstring(expr, from, to)               => ???
    case ETrim(expr, isStarting)                  => ???
    case ERef(ref)                                => eval(ref)
    case EUnary(uop, expr)                        => eval(uop, expr)
    case EBinary(bop, left, right)                => eval(bop, left, right)
    case EVariadic(vop, exprs)                    => eval(vop, exprs)
    case EMathOp(mop, exprs)                      => ???
    case EConvert(cop, expr)                      => ???
    case EExists(ref)                             => ???
    case ETypeOf(base)                            => ???
    case EInstanceOf(expr, target)                => ???
    case ETypeCheck(expr, ty)                     => ???
    case ESizeOf(expr)                            => ???
    case EClo(fname, captured)                    => ???
    case ECont(fname)                             => ???
    case EDebug(expr)                             => ???
    case ERandom()                                => ???
    case ESyntactic(name, args, rhsIdx, children) => ???
    case ELexical(name, expr)                     => ???
    case ERecord(tname, pairs)                    => ???
    case EMap(ty, pairs)                          => ???
    case EList(exprs)                             => ???
    case ECopy(obj)                               => ???
    case EKeys(map, intSorted)                    => ???
    case EMath(n)                                 => SMath(n)
    case EInfinity(pos)                           => SInfinity(pos)
    case ENumber(double)                          => SNumber(double)
    case EBigInt(bigInt)                          => SBigInt(bigInt)
    case EStr(str)                                => SStr(str)
    case EBool(b)                                 => SBool(b)
    case EUndef()                                 => SUndef
    case ENull()                                  => SNull
    case EEnum(name)                              => SEnum(name)
    case ECodeUnit(c)                             => SCodeUnit(c)

  // symbolic execution of a binary operator
  private def eval(bop: BOp, left: Expr, right: Expr): SymExpr =
    import BOp.*
    bop match
      case Eq    => SEq(eval(left), eval(right))
      case Equal => SEqual(eval(left), eval(right))
      case Lt    => SLt(eval(left), eval(right))
      case And   => SAnd(eval(left), eval(right))
      case Or    => SOr(eval(left), eval(right))
      case _     => SOp(bop, List(eval(left), eval(right)))

  private def eval(uop: UOp, expr: Expr): SymExpr =
    import UOp.*
    uop match
      case Not => SNot(eval(expr))
      case _   => SOp(uop, List(eval(expr)))

  private def eval(vop: VOp, exprs: List[Expr]): SymExpr =
    SOp(vop, exprs.map(eval))

  // symbolic execution of a reference
  private def eval(ref: Ref): SymExpr = ref match
    case x: Local                => env.getOrElse(x, SUndef)
    case Global(name)            => ???
    case Field(base, EStr(name)) => ???
    case Field(base, idx)        => ???

  // candidates nodes for symbolic execution
  private def isCandidate(n: Node): Boolean = ???

  // candidates functions for symbolic execution
  private def isCandidate(f: Func): Boolean =
    f == targetFunc ||
    cfg.callerOfTrans(targetFunc).contains(f)

  // ---------------------------------------------------------------------------
  // helper functions for state management
  // ---------------------------------------------------------------------------
  // initialize
  private def enterFunc(func: Func): Unit = {
    node = func.builtinEntry.getOrElse(func.entry)
    func.head match {
      // built-in functions
      case Some(h: BuiltinHead) =>
        import ParamKind.*
        // environment for built-in functions
        env = Map(
          NAME_THIS -> SThis,
          NAME_ARGS_LIST -> SArgsList,
          NAME_NEW_TARGET -> SNewTarget,
        )
        val ps = h.params.zipWithIndex
        for {
          (p, i) <- ps
          sexpr = if (p.kind == Variadic) SArgsList else SArg(i)
        } env += Name(p.name) -> sexpr
        // symbolic environment for built-in functions
        symEnv = SymEnv(
          SThis -> Shape(ESValueT),
          SArgsList -> Shape(ListT(ESValueT)),
          SNewTarget -> Shape(ESValueT),
        ) ++ (for ((p, i) <- ps if p.kind != Variadic) yield {
          SArg(i) -> Shape(ESValueT)
        })
      case _ =>
        val ps = func.params.zipWithIndex
        env = ps.map { (p, i) => p.lhs -> SArg(i) }.toMap
        symEnv = SymEnv(for ((p, i) <- ps) yield SArg(i) -> Shape(p.ty.ty))
    }
    funcs += func
    loops = Set.empty
  }

  def getState: State = State(node, env, prev, funcs, loops, symEnv)

  // pop the previous state and backtrack
  def pop: Unit = ???

  // push the current state and explore the next branch
  def push(branch: Branch, sexpr: SymExpr, side: Boolean): Unit =
    prev = Some(Cond(branch, side), getState)
    symEnv = Solver.add(symEnv, sexpr, side)
}

object SymInterp {
  // factory method
  def apply(
    entryFunc: Func,
    target: Cond,
  )(using cfg: CFG): SymInterp =
    new SymInterp(cfg, entryFunc, target)

  // state of symbolic execution
  case class State(
    node: Node,
    env: Map[Local, SymExpr],
    prev: Option[(Cond, State)],
    funcs: Set[Func],
    loops: Set[Branch],
    symEnv: SymEnv,
  ) {
    def path: List[Cond] = prev.map { (c, s) => c :: s.path }.getOrElse(Nil)
    override def toString: String = stringify(this)
  }

  given stateRule: Rule[State] = (app, st) => {
    app.wrap {
      app :> s"Node: ${st.node.id}"
      app :> s"Env: "
      if (st.env.nonEmpty) app.wrap {
        for ((k, v) <- st.env.toList.sortBy(_._1.toString))
          app :> s"${k} -> ${v}"
      }
      app :> s"SymEnv: " >> st.symEnv
      app :> s"Path: "
      val path = st.path
      if (path.nonEmpty) app.wrap {
        for (cond <- st.path.reverse)
          app :> s"${cond.branch.id}(${cond.cond})"
      }
      app :> s"Funcs: ${st.funcs.map(_.id).mkString(", ")}"
      app :> s"Loops: ${st.loops.map(_.id).mkString(", ")}"
    }
  }

  // found valid path and formula
  enum Result extends Exception:
    case Found(state: State)
    case NotFound

}
