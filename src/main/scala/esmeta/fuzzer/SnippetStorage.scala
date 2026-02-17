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

  /** cache snippets from successful mutation covering abrupt branches */
  def cache(
    touchedCondViews: Map[CondView, Set[Target]],
    snippet: Snippet,
  ): Unit = for {
    (cv, _) <- touchedCondViews
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
      .collect { case c: Call => c.callInst }
      .collectFirst {
        case ICall(_, EClo(fname, _), _) => fname
        case ICall(_, ECont(fname), _)   => fname
        case ISdoCall(_, _, fname, _)    => fname
      }
}
