package esmeta.fuzzer

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.ir.{Func => IRFunc, *}
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

  private val cached: MMap[String, MSet[Snippet]] = MMap()
  private val sdoCalleeCache: MMap[Int, String] = MMap()

  /** get snippets for a function */
  def getSnippets(fname: String): Iterable[Snippet] =
    cached.getOrElse(fname, MSet())

  /** get all snippets for each functions as JSON */
  def dumpContent: Json = JsonObject.fromIterable {
    cached.toSeq.sortBy(_._1).map {
      case (fname, snippets) =>
        val stringified = snippets.map(_.toStr).toSeq.distinct.sorted
        fname -> stringified.asJson
    }
  }.asJson

  /** record SDO callees from interpreter execution */
  def recordSdoCallees(sdoCallees: Map[Int, String]): Unit =
    sdoCalleeCache ++= sdoCallees

  /** cache snippets from successful mutation covering abrupt branches */
  def cache(interp: Interp, snippet: Snippet): Unit = for {
    (cv, _) <- interp.touchedCondViews
    Cond(branch, cond) = cv.cond
    if branch.isAbruptNode && cond
    fname <- findSourceFunc(branch)
  } cached.getOrElseUpdate(fname, MSet()) += snippet

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
