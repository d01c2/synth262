package synth262.fuzzer.mutator

import synth262.es.*
import synth262.es.util.{Walker => AstWalker, *}
import synth262.fuzzer.*
import synth262.util.BaseUtils.*
import synth262.fuzzer.synthesizer.{Synthesizer, RandomSynthesizer}
import synth262.cfg.CFG

/** A random ECMAScript AST mutator */
class RandomMutator(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Mutator.*, RandomMutator.*, Coverage.*

  /** synthesizer */
  val synthesizer = synBuilder(cfg.grammar)

  val names = List("RandomMutator")

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    // count of mutation target asts
    val k = targetAstCounter(ast)
    if (k > 0) {
      c = (n - 1) / k + 1
      shuffle(Walker.walk(ast)).take(n)
    } else List.fill(n)(ast)

  /** number of new candidates to make for each target */
  private var c = 0

  /** internal walker */
  object Walker extends Util.AdditiveListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      val mutants = super.walk(ast)
      if (isTarget(ast))
        val manual = shuffle(manuals(ast)).take(c).toList
        val synthesized = List.tabulate(c) { _ => synthesizer(ast) }
        manual ++ synthesized ++ mutants
      else mutants
    override def walk(lex: Lexical): List[Lexical] =
      manualLexicalMap.get(lex.name) match
        case Some(values) => values.map(Lexical(lex.name, _))
        case None         => List(lex)
  }
}
object RandomMutator {
  // true if the given ast is target ast
  def isTarget(ast: Ast): Boolean = List(
    "AssignmentExpression",
    "PrimaryExpression",
    "Statement",
    "Declaration",
  ).contains(ast.name)

  // count the number of predefined target asts
  val targetAstCounter = new Util.AstCounter(isTarget)
}
