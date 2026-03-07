package esmeta.fuzzer.mutator

import esmeta.es.*
import esmeta.es.util.{Walker => AstWalker, *}
import esmeta.fuzzer.*
import esmeta.util.BaseUtils.*
import esmeta.fuzzer.synthesizer.*
import esmeta.cfg.CFG

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
        val manuals =
          if (ast.name == "AssignmentExpression")
            val nullish = List("null", "undefined")
            val symbols = List("Symbol()", "Symbol.iterator")
            val empties = List("\"\"", "[]", "{}")
            val numericEdges = List(
              "-0.1",
              "-0",
              "-1",
              "-0n",
              "-1n",
              "NaN",
              "Infinity",
              "-Infinity",
              "Number.MAX_SAFE_INTEGER",
              "Number.MIN_SAFE_INTEGER",
              "Number.MAX_SAFE_INTEGER + 1",
              "Number.MAX_VALUE",
              "-Number.MAX_VALUE",
              "Number.MIN_VALUE",
              "-Number.MIN_VALUE",
              "Number.EPSILON",
            )
            (nullish ++ symbols ++ empties ++ numericEdges)
              .map(esParser("AssignmentExpression", ast.args).from)
              .map(_.asInstanceOf[Syntactic])
          else Nil
        val synthesized = List.tabulate(c) { _ => synthesizer(ast) }
        manuals ++ synthesized ++ mutants
      else mutants
    override def walk(lex: Lexical): List[Lexical] =
      lex.name match
        case "BooleanLiteral" =>
          List("true", "false").map(Lexical(lex.name, _))
        case "NumericLiteral" =>
          List("0", "1", "0.1", "0n", "1n").map(Lexical(lex.name, _))
        case "StringNumericLiteral" =>
          List("Infinity", "-Infinity", "0", "-0").map(Lexical(lex.name, _))
        case _ => List(lex)
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
