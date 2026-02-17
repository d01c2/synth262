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
  import Mutator.*, RandomMutator.*, Coverage.*, Snippet.*

  /** synthesizer */
  val synthesizer = synBuilder(cfg.grammar)

  val names = List("RandomMutator")

  /** mutate code */
  def apply(
    code: Code,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Result] = code match
    case Code.Normal(str) =>
      val ast = scriptParser.from(str)
      apply(ast, n, target).map { (mutatedAst, snippet) =>
        val mutatedStr = mutatedAst.toString(grammar = Some(cfg.grammar))
        Result(name, Code.Normal(mutatedStr), snippet)
      }
    case builtin: Code.Builtin =>
      val (preStmts, postStmts) = (builtin.preStmts, builtin.postStmts)
      if ((preStmts.isDefined || postStmts.isDefined) && randBool) {
        // mutate statements
        (preStmts, postStmts) match
          case (Some(_), Some(_)) =>
            if randBool then builtin.mutatePreStmts(n, target)
            else builtin.mutatePostStmts(n, target)
          case (Some(_), None) => builtin.mutatePreStmts(n, target)
          case (None, Some(_)) => builtin.mutatePostStmts(n, target)
          case (None, None)    => raise("unreachable")
      } else {
        // mutate builtin call arguments
        builtin.mutateArgStr(n, target)
      }

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[(Ast, Option[Snippet])] =
    // count of mutation target asts
    val k = targetAstCounter(ast)
    if (k > 0) {
      c = (n - 1) / k + 1
      shuffle(Walker.walk(ast)).take(n)
    } else List.fill(n)((ast, None))

  /** number of new candidates to make for each target */
  private var c = 0

  /** internal walker */
  object Walker extends Util.AdditiveListWalker {
    override def walk(ast: Syntactic): List[(Syntactic, Option[Snippet])] =
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
              .map(ast => (ast.asInstanceOf[Syntactic], Some(AstSnippet(ast))))
          else Nil
        val synthesized = List.tabulate(c) { _ =>
          val newAst = synthesizer(ast)
          (newAst, Some(AstSnippet(newAst)))
        }
        manuals ++ synthesized ++ mutants
      else mutants
    override def walk(lex: Lexical): List[(Lexical, Option[Snippet])] =
      lex.name match
        case "BooleanLiteral" =>
          List("true", "false").map { b =>
            val newAst = Lexical(lex.name, b)
            (newAst, Some(AstSnippet(newAst)))
          }
        case "NumericLiteral" =>
          List("0", "1", "0.1", "0n", "1n").map { n =>
            val newAst = Lexical(lex.name, n)
            (newAst, Some(AstSnippet(newAst)))
          }
        case "StringNumericLiteral" =>
          List("Infinity", "-Infinity", "0", "-0").map { s =>
            val newAst = Lexical(lex.name, s)
            (newAst, Some(AstSnippet(newAst)))
          }
        case _ => List((lex, None))
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
