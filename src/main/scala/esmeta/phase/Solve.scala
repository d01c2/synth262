package esmeta.phase

import esmeta.*
import esmeta.cfg.*
import esmeta.es.util.Coverage
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{Func => _, *}
import esmeta.solver.*
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.util.*
import esmeta.util.BaseUtils.*

/** `solve` phase */
case object Solve extends Phase[CFG, String] {
  val name = "solve"
  val help = "generates an ECMAScript program that covers a target branch"

  def apply(cfg: CFG, cmdConfig: CommandConfig, config: Config): String =
    val id = config.branch.getOrElse(raise("solve: branch id is required"))
    val branch = cfg.nodeMap.get(id) match
      case Some(b: Branch) => b
      case _               => raise(s"solve: node $id is not a branch")

    val func = cfg.funcOf(branch)
    val conds: List[Cond] = config.side match
      case Some(side) => List(Cond(branch, side))
      case None       => List(Cond(branch, true), Cond(branch, false))

    conds
      .map { cond =>
        solve(cfg, func, branch, cond).headOption match
          case Some(js) => s"[solve] $cond: $js"
          case None     => s"[solve] $cond: no solution"
      }
      .mkString("\n")

  /** path enumeration -> symbolic interpretation -> solving -> JS */
  def solve(
    cfg: CFG,
    func: Func,
    branch: Branch,
    cond: Cond,
  ): LazyList[String] =
    val paths = PathEnumerator(func, branch)
    val params = entryParams(func)
    val goals = LazyList.from(paths).flatMap { path =>
      SymbolicInterpreter(cfg, func, path, cond)
    }
    goals.flatMap { goal =>
      Solver.solve(goal, params).flatMap { witness =>
        Reify.toJsCall(func, params, witness)
      }
    }

  def entryParams(func: Func): List[String] =
    val irParams =
      func.irFunc.params.map(_.lhs.name).filterNot(_ == ARGS_LIST_STR)
    val builtinArgs = func.head.toList.collect {
      case head: BuiltinHead =>
        head.params.collect { case p if p.kind != ParamKind.Variadic => p.name }
    }.flatten
    (irParams ++ builtinArgs).distinct

  def defaultConfig: Config = Config()
  val options: List[PhaseOption[Config]] = List(
    (
      "branch",
      NumOption((c, k) => c.branch = Some(k)),
      "solve for the given branch id.",
    ),
    (
      "side",
      BoolOption((c, b) => c.side = Some(b)),
      "solve only the given side (default: both).",
    ),
  )
  case class Config(
    var branch: Option[Int] = None,
    var side: Option[Boolean] = None,
  )
}
