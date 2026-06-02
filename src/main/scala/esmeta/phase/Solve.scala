package esmeta.phase

import esmeta.*
import esmeta.cfg.*
import esmeta.es.util.Coverage.Cond
import esmeta.ir.{Func => _, *}
import esmeta.solver.*
import esmeta.spec.{BuiltinHead, ParamKind}
import esmeta.util.*
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Set => MSet, Queue}

/** `solve` phase */
case object Solve extends Phase[CFG, String] {
  val name = "solve"
  val help = "generates an ECMAScript program that covers a target branch"

  def apply(cfg: CFG, cmdConfig: CommandConfig, config: Config): String =
    given CFG = cfg
    val id = config.branch.getOrElse(raise("solve: branch id is required"))
    val branch = cfg.nodeMap.get(id) match
      case Some(b: Branch) => b
      case _               => raise(s"solve: node $id is not a branch")
    val conds: List[Cond] = config.side match
      case Some(side) => List(Cond(branch, side))
      case None       => List(Cond(branch, true), Cond(branch, false))

    val entries = findEntries(branch)

    conds
      .map { cond =>
        LazyList.from(entries).flatMap(solve(_, branch, cond)).headOption match
          case Some(js) => s"[solve] $cond: $js"
          case None     => s"[solve] $cond: no solution"
      }
      .mkString("\n")

  def findEntries(branch: Branch)(using cfg: CFG): List[Func] =
    val func = cfg.funcOf(branch)
    if (func.isBuiltin) List(func)
    else {
      val reached = MSet(func)
      val queue = Queue(func)
      while (queue.nonEmpty) {
        for {
          caller <- cfg.callerOf.getOrElse(queue.dequeue(), Set.empty)
          if reached.add(caller)
        } queue.enqueue(caller)
      }
      reached.filter(_.isBuiltin).toList
    }

  /** symbolic walk -> constraint solving -> JS reification */
  def solve(
    entry: Func,
    branch: Branch,
    cond: Cond,
  )(using CFG): LazyList[String] =
    val params = paramIds(entry)
    var goalIdx = 0
    println(s"\n=== Entry: ${entry.name} ===")
    val goals = SymbolicInterpreter(
      entry,
      cond,
      goal => {
        goalIdx += 1
        println(s"\n--- Goal $goalIdx [raw] ---")
        goal.foreach(f => println(s"  $f"))
        val rw = Solver.rewrite(goal)
        println(s"--- Goal $goalIdx [rewritten] ---")
        rw.foreach(f => println(s"  $f"))
        val solved = Solver.solveAll(goal)
        if (solved.isEmpty) {
          println(s"--- Goal $goalIdx => CONTRADICTION ---")
          LazyList.empty
        } else {
          val first = solved.head
          println(s"--- Goal $goalIdx [simplified] ---")
          first.foreach(f => println(s"  $f"))
          solved
        }
      },
    ).result
    goals.flatMap { solved =>
      Reify(solved, params).witness.flatMap { witness =>
        Reify.toJsCall(entry, params, witness)
      }
    }

  def paramIds(func: Func): List[Sym] =
    val irIds = func.irFunc.params.flatMap { p =>
      p.lhs.name match
        case "this"      => Some(Sym.This)
        case "NewTarget" => Some(Sym.NewTarget)
        case _           => None
    }
    val headIds = func.head match
      case Some(h: BuiltinHead) =>
        h.params
          .collect { case p if p.kind != ParamKind.Variadic => p }
          .zipWithIndex
          .map((_, k) => Sym.Arg(k))
      case _ => Nil
    (irIds ++ headIds).distinct

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
