package esmeta.fuzzer

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.ir.*
import io.circe.*, io.circe.syntax.*
import scala.collection.mutable.{Map => MMap, Set => MSet}

/** Snippet kind classification */
enum SnippetKind {
  case Expression
  case Statement
  case Declaration
}

/** Snippet for mutation (kind + string representation) */
case class Snippet(kind: SnippetKind, str: String)

/** Storage for abrupt-triggering code snippets */
class SnippetStorage(using val cfg: CFG) {
  import Coverage.*

  /** production names derived from grammar chains */
  private lazy val (expressionNames, statementNames, declarationNames) = {
    import esmeta.spec.ProductionKind
    val grammar = cfg.grammar
    val syntacticNames = grammar.prods.collect {
      case p if p.kind == ProductionKind.Syntactic => p.name
    }.toSet
    def chainChildren(prodName: String): Set[String] =
      (for {
        prod <- grammar.nameMap.get(prodName).toSet
        rhs <- prod.rhsVec
        requiredNts = rhs.ntsWithOptional.collect {
          case (nt, false) if syntacticNames(nt.name) => nt.name
        }
        if requiredNts.size == 1
      } yield requiredNts.head).toSet
    def reachable(isRoot: String => Boolean): Set[String] =
      val roots = syntacticNames.filter(isRoot)
      val queue = scala.collection.mutable.Queue(roots.toSeq*)
      val visited = MSet(roots.toSeq*)
      while (queue.nonEmpty)
        val name = queue.dequeue()
        for {
          child <- chainChildren(name)
          if !visited(child)
        } {
          visited += child
          queue.enqueue(child)
        }
      visited.toSet
    (
      reachable(_.endsWith("Expression")),
      reachable(_.endsWith("Statement")),
      reachable(_.endsWith("Declaration")),
    )
  }

  /** classify AST production name into snippet kind */
  // NOTE: prioritize expression over statement and declaration
  def classify(prodName: String): Option[SnippetKind] =
    if expressionNames(prodName) then Some(SnippetKind.Expression)
    else if statementNames(prodName) then Some(SnippetKind.Statement)
    else if declarationNames(prodName) then Some(SnippetKind.Declaration)
    else None

  /** check if snippet kind is compatible with target production */
  def isCompatible(kind: SnippetKind, targetProdName: String): Boolean =
    classify(targetProdName).contains(kind)

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

  /** cache localized snippets that triggered abrupt branches */
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
            .flatMap { ast =>
              classify(ast.name).map { kind =>
                Snippet(kind, ast.toString(grammar = Some(cfg.grammar)))
              }
            }
        case Target.BuiltinThis(thisArg) =>
          Some(Snippet(SnippetKind.Expression, thisArg))
        case Target.BuiltinArg(arg, _) =>
          Some(Snippet(SnippetKind.Expression, arg))
      }
      if (localized.nonEmpty)
        val map = snippetsByFunc.getOrElseUpdate(calleeId, MMap())
        updateShortest(map, branch.id, localized.minBy(_.str.length))
    }

    for {
      (fid, snippets) <- snippetsByFunc
      branchIds = calleeIndex.getOrElseUpdate(fid, MSet())
      (branchId, snippet) <- snippets
      if branchIds.size < 100
      if cached.get(branchId).forall(_.str.length > snippet.str.length)
    } {
      cached(branchId) = snippet
      branchIds += branchId
      cacheLog(branchId) = CacheEvent(fid, mutant.toString, snippet.str)
    }

  /** update map entry only if the new snippet is shorter */
  private def updateShortest(
    map: MMap[Int, Snippet],
    key: Int,
    snippet: Snippet,
  ): Unit =
    if (map.get(key).forall(_.str.length > snippet.str.length))
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
