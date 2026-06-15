package esmeta.solver

import esmeta.cfg.*
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{Func => _, *}
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.util.*

class SymbolicInterpreter(
  cfg: CFG,
  entryFunc: Func,
  target: Cond,
) {
  import SymbolicInterpreter.*, Result.*

  lazy val result: Option[(Path, Formula)] = execute

  // node for symbolic execution
  var node: Node = entryFunc.entry
  // current path constraint for symbolic execution
  var constraint: List[SymExpr] = Nil
  // environment for symbolic execution
  var env: Map[Local, SymExpr] = Map.empty
  // previous states for backtracking
  var prev: Option[(Cond, State)] = None
  // functions encountered during symbolic execution
  var funcs: Set[Func] = Set.empty
  // loops encountered during symbolic execution
  var loops: Set[Branch] = Set.empty

  // target
  val targetFunc: Func = cfg.funcOf(target.branch)

  // ---------------------------------------------------------------------------
  // Helper functions for symbolic execution
  // ---------------------------------------------------------------------------
  // main symbolic execution loop
  private def execute: Option[(Path, Formula)] = {
    if (!isCandidate(entryFunc)) return None
    enterFunc(entryFunc)
    try {
      while (true) step
      None
    } catch {
      case Found(path, formula) => Some((path, formula))
      case NotFound             => None
      case e: Throwable         => throw e
    }
  }

  // symbolic execution of a node
  private def step: Unit = {
    // -------------------------------------------------------------------------
    // XXX: remove
    // -------------------------------------------------------------------------
    println("-" * 80)
    println(s"Executing node ${node.name}:")
    showState
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
        val sexpr = if (target.cond) eval(branch.cond) else !eval(branch.cond)
        val formula = constraint.foldLeft(sexpr)(SAnd(_, _))
        ???
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
  // Helper functions for state management
  // ---------------------------------------------------------------------------
  // initialize
  private def enterFunc(func: Func): Unit = {
    node = func.builtinEntry.getOrElse(func.entry)
    env = func.params.zipWithIndex.map { (p, i) => p.lhs -> SArg(i) }.toMap
    for {
      case h: BuiltinHead <- func.head.toList
      _ = env ++= List(
        NAME_THIS -> SThis,
        NAME_ARGS_LIST -> SArgsList,
        NAME_NEW_TARGET -> SNewTarget,
      )
      (p, i) <- h.params.zipWithIndex
      sexpr = if (p.kind == ParamKind.Variadic) SArgsList else SArg(i)
    } env += Name(p.name) -> sexpr
    funcs += func
    loops = Set.empty
  }

  // pop the previous state and backtrack
  def pop: Unit = ???

  // push the current state and explore the next branch
  def push(branch: Branch, sexpr: SymExpr, taken: Boolean): Unit =
    val state = State(node, constraint, env, prev, funcs, loops)
    constraint ::= (if (taken) sexpr else !sexpr)
    prev = Some(Cond(branch, taken), state)

  private def showState: Unit = {
    println(s"- Node: ${node.id}")
    println(s"- Constraint: ${constraint.mkString(" /\\ ")}")
    println(s"- Env: {")
    for ((k, v) <- env.toList.sortBy(_._1.toString))
      println(s"    ${k} -> ${v}")
    println("  }")
    println(
      s"- Prev: ${prev.map { (c, s) => s"<$c, ...>" }.getOrElse("")}",
    )
    println(s"- Funcs: ${funcs.map(_.id).mkString(", ")}")
    println(s"- Loops: ${loops.map(_.id).mkString(", ")}")
  }
}

object SymbolicInterpreter {
  // factory method
  def apply(
    entryFunc: Func,
    target: Cond,
  )(using cfg: CFG): SymbolicInterpreter =
    new SymbolicInterpreter(cfg, entryFunc, target)

  // path of symbolic execution
  case class Path(entryFunc: Func, conds: List[Cond])

  // state of symbolic execution
  case class State(
    node: Node,
    constraint: List[SymExpr],
    env: Map[Local, SymExpr],
    prev: Option[(Cond, State)],
    funcs: Set[Func],
    loops: Set[Branch],
  )

  // found valid path and formula
  enum Result extends Exception:
    case Found(path: Path, formula: Formula)
    case NotFound
}
