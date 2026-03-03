package esmeta.fuzzer.mutator

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.*
import esmeta.util.BaseUtils.*
import scala.util.Try

/** A mutator targeting abrupt completion branches */
class AbruptMutator(using cfg: CFG, snippetStorage: SnippetStorage)
  extends Mutator {
  import Mutator.*, Coverage.*

  val targetMutator = TargetMutator()
  val names = "AbruptMutator" :: targetMutator.names

  /** mutate code */
  def apply(
    code: Code,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Result] = (for {
    (cv, cov) <- target
    CondView(cond, view) = cv
    branch = cond.branch
    // NOTE: mutate if we "should make" abrupt completion case
    if branch.isAbruptNode && !cond.cond
    fid <- snippetStorage.findSourceFunc(branch)
    snippets = snippetStorage.getSnippets(fid)
    if snippets.nonEmpty
    targets = cov.targetCondViews.getOrElse(cond, Map()).getOrElse(view, Set())
  } yield {
    val results = for {
      snippet <- snippets
      t <- targets
      result <- mutate(code, t, snippet)
    } yield result
    val mutants = shuffle(results.toSeq).take(n)
    mutants ++ targetMutator(code, n - mutants.size, target)
  }).getOrElse(targetMutator(code, n, target))

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    targetMutator(ast, n, target)

  /** apply snippet to target */
  private def mutate(
    code: Code,
    target: Target,
    snippet: Snippet,
  ): Option[Result] = (code, target) match
    case (Code.Normal(str), t: Target.Normal)
        if snippetStorage.isCompatible(snippet.kind, t.prodName) =>
      for {
        mutatedAst <- Walker(t, snippet.str)
          .walk(scriptParser.from(str))
          .headOption
      } yield {
        val mutant =
          Code.Normal(mutatedAst.toString(grammar = Some(cfg.grammar)))
        Result(name, mutant)
      }
    case (b: Code.Builtin, Target.BuiltinThis(thisArg)) =>
      if (b.thisArg == Some(thisArg))
        Some(Result(name, b.replace(target, snippet.str)))
      else None
    case (b: Code.Builtin, Target.BuiltinArg(arg, i)) =>
      if (b.args.lift(i) == Some(arg))
        Some(Result(name, b.replace(target, snippet.str)))
      else None
    case _ => None

  /** walker that re-parses snippet at target production level */
  class Walker(normalTarget: Target.Normal, snippetStr: String)
    extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      if (ast.matches(normalTarget))
        Try(
          cfg
            .esParser(ast.name, ast.args)
            .from(snippetStr)
            .asInstanceOf[Syntactic],
        ).toOption.toList
      else super.walk(ast)
  }
}
