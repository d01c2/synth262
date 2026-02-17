package esmeta.fuzzer.mutator

import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.*
import esmeta.util.BaseUtils.*
import esmeta.cfg.CFG
import esmeta.parser.{ESParser, AstFrom}

/** ECMAScript AST mutator */
trait Mutator(using val cfg: CFG) {
  import Mutator.*, Coverage.*, Snippet.*

  /** ECMAScript parser */
  lazy val esParser: ESParser = cfg.esParser
  lazy val scriptParser: AstFrom = esParser("Script")
  lazy val argListParser: AstFrom = esParser("ArgumentList", List(false, false))

  /** mutate code */
  def apply(
    code: Code,
    target: Option[(CondView, Coverage)],
  ): Result = apply(code, 1, target).head
  def apply(
    code: Code,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Result]

  /** mutate string */
  def apply(
    str: String,
    target: Option[(CondView, Coverage)],
  ): String = apply(str, 1, target).head
  def apply(
    str: String,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[String] = apply(scriptParser.from(str), n, target)
    .map((ast, _) => ast.toString(grammar = Some(cfg.grammar)))

  /** mutate AST */
  def apply(
    ast: Ast,
    target: Option[(CondView, Coverage)],
  ): Ast = apply(ast, 1, target).head._1
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[(Ast, Option[Snippet])]

  /** Possible names of underlying mutators */
  val names: List[String]
  lazy val name: String = names.head

  /** helper for mutation in builtin code */
  extension (builtin: Code.Builtin) {
    def mutatePreStmts(
      n: Int,
      target: Option[(CondView, Coverage)],
    ): Seq[Result] = for {
      preStmts <- builtin.preStmts.toSeq
      ast = scriptParser.from(preStmts)
      (mutatedAst, snippet) <- apply(ast, n, target)
      mutatedStmts = mutatedAst.toString(grammar = Some(cfg.grammar))
    } yield Result(name, builtin.copy(preStmts = Some(mutatedStmts)), snippet)
    def mutatePostStmts(
      n: Int,
      target: Option[(CondView, Coverage)],
    ): Seq[Result] = for {
      postStmts <- builtin.postStmts.toSeq
      ast = scriptParser.from(postStmts)
      (mutatedAst, snippet) <- apply(ast, n, target)
      mutatedStmts = mutatedAst.toString(grammar = Some(cfg.grammar))
    } yield Result(name, builtin.copy(postStmts = Some(mutatedStmts)), snippet)

    /** Mutate ALL builtin args exhaustively */
    def mutateArgStr(
      n: Int,
      target: Option[(CondView, Coverage)],
    ): Seq[Result] = mutateTargets(builtin.targetArgs, n, target)

    /** Mutate specific builtin targets */
    def mutateTargets(
      targets: Seq[Target],
      n: Int,
      target: Option[(CondView, Coverage)],
    ): Seq[Result] =
      if (targets.nonEmpty)
        // Exhaustive: mutate ALL targets, distribute n across them
        val numTargets = targets.size
        val perTarget = (n + numTargets - 1) / numTargets
        targets.flatMap { mutationCite =>
          val argStr = mutationCite.argStr
          val argAst = argListParser.from(argStr)
          for {
            (mutatedAst, _) <- apply(argAst, perTarget, target)
            mutatedStr = mutatedAst.toString(grammar = Some(cfg.grammar))
            mutatedCode = builtin.replace(mutationCite, mutatedStr)
          } yield Result(name, mutatedCode, Some(StrSnippet(mutatedStr)))
        }
      else List.fill(n)(Result(name, builtin, None))
  }
}

object Mutator {
  import Code.*, Target.*

  /** Result of mutation with mutator name and code */
  case class Result(name: String, code: Code, snippet: Option[Snippet])

  /** Update the builtin code with the given string at the target position */
  extension (builtin: Builtin) {
    def replace(target: Target, str: String): Builtin = target match
      case BuiltinThis(_)   => builtin.copy(thisArg = Some(str))
      case BuiltinArg(_, i) => builtin.copy(args = builtin.args.updated(i, str))
      case _                => raise("target must be builtin")
  }
}
