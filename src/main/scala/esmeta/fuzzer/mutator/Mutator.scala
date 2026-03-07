package esmeta.fuzzer.mutator

import esmeta.es.*
import esmeta.es.util.*
import esmeta.util.BaseUtils.*
import esmeta.cfg.CFG
import esmeta.parser.{ESParser, AstFrom}

/** ECMAScript AST mutator */
trait Mutator(using val cfg: CFG) {
  import Mutator.*, Coverage.*

  /** ECMAScript parser */
  lazy val esParser: ESParser = cfg.esParser
  lazy val scriptParser: AstFrom = esParser("Script")

  /** mutate code */
  def apply(
    code: String,
    target: Option[(CondView, Coverage)],
  ): Result = apply(code, 1, target).head
  def apply(
    code: String,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Result] =
    val ast = scriptParser.from(code)
    apply(ast, n, target).map { mutatedAst =>
      val s = mutatedAst.toString(grammar = Some(cfg.grammar))
      Result(name, s)
    }

  /** mutate AST */
  def apply(
    ast: Ast,
    target: Option[(CondView, Coverage)],
  ): Ast = apply(ast, 1, None).head
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast]

  /** Possible names of underlying mutators */
  val names: List[String]
  lazy val name: String = names.head
}

object Mutator {

  /** Result of mutation with mutator name and code */
  case class Result(name: String, code: String)
}
