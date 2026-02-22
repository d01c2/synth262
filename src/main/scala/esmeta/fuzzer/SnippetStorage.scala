package esmeta.fuzzer

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.ir.*
import io.circe.*, io.circe.syntax.*
import scala.collection.mutable.{Map => MMap, Set => MSet}

/** Snippet for mutation (ast for normal code, string for builtin code) */
enum Snippet {
  case AstSnippet(ast: Ast)
  case StrSnippet(str: String)

  def toStr(using cfg: CFG): String = this match
    case StrSnippet(str) => str
    case AstSnippet(ast) => ast.toString(grammar = Some(cfg.grammar))
}

/** Storage for abrupt-triggering code snippets */
class SnippetStorage(using val cfg: CFG) {
  import Coverage.*

  /** fname -> branchId -> shortest snippet per branch */
  private val cached: MMap[String, MMap[Int, Snippet]] = MMap()
  private val sdoCalleeCache: MMap[Int, String] = MMap()
  private val forwardEdges: MMap[String, MSet[String]] = MMap()

  /** cache event log for debugging — only entries that made it into cached */
  private case class CacheEvent(
    sourceFunc: String,
    caller: String,
    mutant: String,
    snippet: String,
  )
  private val cacheLog: MMap[Int, CacheEvent] = MMap()

  /** get snippets for a function (direct + 1-level callee lookup) */
  def getSnippets(fname: String): Iterable[Snippet] =
    val direct = cached.getOrElse(fname, MMap()).values
    val fromCallees = forwardEdges.getOrElse(fname, MSet()).flatMap { callee =>
      cached.getOrElse(callee, MMap()).values
    }
    direct ++ fromCallees

  /** dump cached snippets with metadata as JSON, keyed by branchId */
  def dumpContent: Json = JsonObject.fromIterable {
    cacheLog.toSeq.sortBy(_._1).map {
      case (branchId, e) =>
        branchId.toString -> JsonObject(
          "sourceFunc" -> e.sourceFunc.asJson,
          "caller" -> e.caller.asJson,
          "mutant" -> e.mutant.asJson,
          "snippet" -> e.snippet.asJson,
        ).asJson
    }
  }.asJson

  /** record SDO callees from interpreter execution */
  def recordSdoCallees(sdoCallees: Map[Int, String]): Unit =
    sdoCalleeCache ++= sdoCallees

  /** cache localized AST snippets that triggered newly covered abrupt branches
    */
  def cache(interp: Interp, mutant: Code): Unit =
    val snippetsByFunc: MMap[String, MMap[Int, Snippet]] = MMap()
    val callerOf: MMap[Int, String] = MMap()

    for {
      (cv, targets) <- interp.touchedCondViews
      CondView(cond, view) = cv
      branch = cond.branch
      // NOTE: cache if we meet abrupt completion case
      if branch.isAbruptNode && cond.cond
      calleeName <- findSourceFunc(branch)
    } {
      // build forward edges from containing function to callee
      val caller = cfg.funcOf(branch).name
      forwardEdges.getOrElseUpdate(caller, MSet()) += calleeName
      callerOf(branch.id) = caller
      val localized: Set[Snippet] = targets.flatMap {
        case n: Target.Normal =>
          interp.st.cachedAst
            .flatMap(findSubtree(_, n))
            .map(Snippet.AstSnippet(_))
        case Target.BuiltinThis(thisArg) => Some(Snippet.StrSnippet(thisArg))
        case Target.BuiltinArg(arg, _)   => Some(Snippet.StrSnippet(arg))
      }
      if (localized.nonEmpty)
        val map = snippetsByFunc.getOrElseUpdate(calleeName, MMap())
        updateShortest(map, branch.id, localized.minBy(_.toStr.length))
    }

    for {
      (fname, snippets) <- snippetsByFunc
      target = cached.getOrElseUpdate(fname, MMap())
      (branchId, snippet) <- snippets
      if target.size < 100
    }
      if target.get(branchId).forall(_.toStr.length > snippet.toStr.length) then
        target(branchId) = snippet
        cacheLog(branchId) = CacheEvent(
          sourceFunc = fname,
          caller = callerOf.getOrElse(branchId, ""),
          mutant = mutant.toString,
          snippet = snippet.toStr,
        )

  /** update map entry only if the new snippet is shorter */
  private def updateShortest(
    map: MMap[Int, Snippet],
    key: Int,
    snippet: Snippet,
  ): Unit =
    if map.get(key).forall(_.toStr.length > snippet.toStr.length) then
      map(key) = snippet

  /** find subtree in AST matching the given target location */
  private def findSubtree(
    ast: Ast,
    target: Target.Normal,
  ): Option[Syntactic] = ast match
    case syn: Syntactic =>
      if (syn.matches(target)) Some(syn)
      else syn.children.flatten.flatMap(findSubtree(_, target)).headOption
    case _ => None

  /** trace branch condition locals to their defining call */
  def findSourceFunc(branch: Branch): Option[String] =
    val func = cfg.funcOf(branch)
    val dataDeps = cfg.depGraph.dataDeps(func)
    val defs = dataDeps.useToDefs(branch)
    defs.values.flatten
      .collect { case c: Call => c }
      .flatMap { c =>
        c.callInst match
          case ICall(_, EClo(fname, _), _) => Some(fname)
          case ICall(_, ECont(fname), _)   => Some(fname)
          case _: ISdoCall                 => sdoCalleeCache.get(c.id)
          case _                           => None
      }
      .headOption
}
