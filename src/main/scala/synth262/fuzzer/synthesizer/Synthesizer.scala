package synth262.fuzzer.synthesizer

import synth262.cfg.*
import synth262.es.util.*
import synth262.es.*
import synth262.spec.Grammar

/** ECMAScript AST synthesizer */
trait Synthesizer {

  /** synthesizer name */
  def name: String

  /** for general production */
  def apply(ast: Ast): Ast = ast match
    case ast: Syntactic => apply(ast)
    case ast: Lexical   => apply(ast)

  /** for syntactic production */
  def apply(
    name: String,
    args: List[Boolean],
    rhsIdx: Option[Int] = None,
  ): Syntactic
  def apply(ast: Syntactic): Syntactic = apply(ast.name, ast.args)

  /** for lexical production */
  def apply(name: String): Lexical
  def apply(ast: Lexical): Lexical = apply(ast.name)
}
object Synthesizer:
  type Builder = Grammar => Synthesizer
