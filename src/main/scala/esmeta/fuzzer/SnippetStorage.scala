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

  /** branchId -> shortest snippet per branch */
  private val cached: MMap[Int, Snippet] = MMap()

  /** calleeId -> set of branchIds (reverse index for getSnippets) */
  private val calleeIndex: MMap[Int, MSet[Int]] = MMap()
  private val sdoCalleeCache: MMap[Int, Int] = MMap()
  private val forwardEdges: MMap[Int, MSet[Int]] = MMap()

  /** cache event log for debugging — only entries that made it into cached */
  private case class CacheEvent(sourceFid: Int, mutant: String, snippet: String)
  private val cacheLog: MMap[Int, CacheEvent] = MMap()

  /** get snippets for a function (direct + 1-level callee lookup) */
  def getSnippets(fid: Int): Iterable[Snippet] =
    val directIds = calleeIndex.getOrElse(fid, MSet())
    val calleeIds = forwardEdges.getOrElse(fid, MSet()).flatMap { callee =>
      calleeIndex.getOrElse(callee, MSet())
    }
    (directIds ++ calleeIds).flatMap(cached.get)

  /** dump cached snippets with metadata as JSON, keyed by branchId */
  def dumpContent: Json = JsonObject.fromIterable {
    cacheLog.toSeq.sortBy(_._1).map {
      case (branchId, e) =>
        branchId.toString -> JsonObject(
          "sourceFunc" -> funcName(e.sourceFid).asJson,
          "mutant" -> e.mutant.asJson,
          "snippet" -> e.snippet.asJson,
        ).asJson
    }
  }.asJson

  /** record SDO callees from interpreter execution */
  def recordSdoCallees(sdoCallees: Map[Int, Int]): Unit =
    sdoCalleeCache ++= sdoCallees

  /** cache localized AST snippets that triggered abrupt branches */
  def cache(interp: Interp, mutant: Code): Unit =
    val snippetsByFunc: MMap[Int, MMap[Int, Snippet]] = MMap()

    for {
      (cv, targets) <- interp.touchedCondViews
      CondView(cond, view) = cv
      branch = cond.branch
      // NOTE: cache if we meet abrupt completion case
      if branch.isAbruptNode && cond.cond
      calleeId <- findSourceFunc(branch)
    } {
      // build forward edges from containing function to callee
      val callerId = cfg.funcOf(branch).id
      forwardEdges.getOrElseUpdate(callerId, MSet()) += calleeId
      val localized: Set[Snippet] = targets.flatMap {
        case n: Target.Normal =>
          interp.st.cachedAst
            .flatMap(findSubtree(_, n))
            .map(Snippet.AstSnippet(_))
        case Target.BuiltinThis(thisArg) => Some(Snippet.StrSnippet(thisArg))
        case Target.BuiltinArg(arg, _)   => Some(Snippet.StrSnippet(arg))
      }
      if (localized.nonEmpty)
        val map = snippetsByFunc.getOrElseUpdate(calleeId, MMap())
        updateShortest(map, branch.id, localized.minBy(_.toStr.length))
    }

    for {
      (fid, snippets) <- snippetsByFunc
      branchIds = calleeIndex.getOrElseUpdate(fid, MSet())
      (branchId, snippet) <- snippets
      if branchIds.size < 100
    }
      if cached.get(branchId).forall(_.toStr.length > snippet.toStr.length) then
        cached(branchId) = snippet
        branchIds += branchId
        cacheLog(branchId) = CacheEvent(
          sourceFid = fid,
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
  def findSourceFunc(branch: Branch): Option[Int] =
    val func = cfg.funcOf(branch)
    val dataDeps = cfg.depGraph.dataDeps(func)
    val defs = dataDeps.useToDefs(branch)
    defs.values.flatten
      .collect { case c: Call => c }
      .flatMap { c =>
        c.callInst match
          case ICall(_, EClo(fname, _), _) => cfg.fnameMap.get(fname).map(_.id)
          case ICall(_, ECont(fname), _)   => cfg.fnameMap.get(fname).map(_.id)
          case _: ISdoCall                 => sdoCalleeCache.get(c.id)
          case _                           => None
      }
      .headOption

  /** resolve function id to name */
  private def funcName(fid: Int): String =
    cfg.funcMap.get(fid).map(_.name).getOrElse(s"unknown($fid)")
}
