package esmeta.llm

import esmeta.*
import esmeta.cfg.*
import esmeta.es.util.*
import esmeta.es.util.Coverage.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.spec.{Algorithm, SyntaxDirectedOperationHead => SdoHead}
import scala.io.Source
import scala.collection.mutable.ListBuffer

/** Prompt Builder */
case class PromptBuilder(cfg: CFG, targetConds: Seq[Cond]) {

  lazy val prefix = Source
    .fromFile(s"$MANUALS_DIR/prompts/prefix.prompt")
    .getLines()
    .mkString("\n")
  lazy val suffix = Source
    .fromFile(s"$MANUALS_DIR/prompts/suffix.prompt")
    .getLines()
    .mkString("\n")

  val callerMap: Map[Func, Set[Func]] = (for {
    caller <- cfg.funcs
    case Call(_, callInst, _) <- caller.nodes
    callee <- getCallees(cfg, callInst)
  } yield (callee, caller))
    .foldLeft(Map.empty[Func, Set[Func]]) {
      case (acc, (callee, caller)) =>
        val prev = acc.getOrElse(callee, Set.empty[Func])
        acc.updated(callee, prev + caller)
    }

  lazy val prompts: Seq[Prompt] =
    for {
      targetCond <- targetConds
      func = cfg.funcOf(targetCond.branch)
      irFunc = func.irFunc
      algo <- irFunc.algo
      loc <- targetCond.loc
    } yield {
      val uncovered = targetCond.neg

      // Trace target related locals and find provenance
      val dataDeps = cfg.depGraph.dataDeps(func)
      val usedLocals = dataDeps.uses(uncovered.branch)
      val defNodes = usedLocals.flatMap { local =>
        dataDeps.useToDefs(uncovered.branch).getOrElse(local, Set())
      }
      val provenances = for {
        case Call(_, callInst, _) <- defNodes
        callees <- getCallees(cfg, callInst)
        algo <- callees.irFunc.algo
      } yield algo

      // Collect call paths that reach target
      lazy val callPaths = getCallPaths(func, callerMap)

      // prompt render helpers
      def section(tag: String, content: String): String =
        s"<$tag>\n${content.trim()}\n</$tag>"

      val targetBranchBlock = s"""
        |- Location: ${algo.normalizedName} Step ${loc.stepString}
        |- Condition: ${uncovered.branch.cond}
        |- Required side: ${uncovered.cond}
        |""".stripMargin

      val targetSpecExcerptBlock = List(
        section("SPEC_EXCERPT", s"$algo"),
        section("IR_EXCERPT", s"$irFunc"),
      ).mkString("\n")

      val callPathsBlock = callPaths.zipWithIndex
        .map {
          case (path, i) =>
            s"${i + 1}. ${path.map(_.normalizedName).mkString(" -> ")}"
        }
        .mkString("\n")

      val refSpecsBlock =
        (provenances ++ callPaths.flatten.toSet - algo).iterator
          .map(a => s"<SPEC_EXCERPT_START>\n$a\n<SPEC_EXCERPT_END>")
          .mkString("\n")

      val body = List(
        section("TARGET_BRANCH", targetBranchBlock),
        section("TARGET_SPEC_EXCERPT", targetSpecExcerptBlock),
        section("CALL_PATHS", callPathsBlock),
        section("REFERENCE_SPEC_EXCERPTS", refSpecsBlock),
      ).mkString("\n\n")

      Prompt(uncovered, List(prefix, body, suffix).mkString("\n\n"))
    }

  private def getCallees(cfg: CFG, inst: CallInst): Set[Func] = inst match
    case ICall(_, fexpr, _) =>
      fexpr match
        case EClo(fname, _) => cfg.funcs.filter(_.name == fname).toSet
        case ECont(fname)   => cfg.funcs.filter(_.name == fname).toSet
        case _              => Set()
    case ISdoCall(_, base, _, _) =>
      base match
        case EClo(fname, _) => cfg.funcs.filter(_.name == fname).toSet
        case ECont(fname)   => cfg.funcs.filter(_.name == fname).toSet
        case _              => Set()

  private def getCallPaths(
    func: Func,
    callerMap: Map[Func, Set[Func]],
    k: Int = 2, // k-call-path-sensitivity
    limit: Int = 5, // get maximum 5 call paths
  ): List[List[Algorithm]] =
    val paths = ListBuffer[List[Func]]()
    def isEntry(f: Func): Boolean = f.isSDO || f.isBuiltin
    def loop(cur: Func, path: List[Func], visited: Set[Func]): Unit = {
      val callers = callerMap.getOrElse(cur, Set())
      if (isEntry(cur) || callers.isEmpty || path.length >= k + 1) {
        paths += path
      } else {
        val sortedCallers = callers.toList.sortBy(_.name)
        for (caller <- sortedCallers if !visited.contains(caller)) {
          loop(caller, caller :: path, visited + caller)
        }
      }
    }
    loop(func, List(func), Set(func))
    paths.toList.take(limit).map(_.flatMap(_.irFunc.algo)).filter(_.nonEmpty)
}
