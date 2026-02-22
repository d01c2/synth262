package esmeta.fuzzer.mutator

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.*
import esmeta.util.BaseUtils.*

/** A mutator targeting abrupt completion branches */
class AbruptMutator(using cfg: CFG, snippetStorage: SnippetStorage)
  extends Mutator {
  import Mutator.*, Coverage.*, Snippet.*

  val randomMutator = RandomMutator()
  val names = "AbruptMutator" :: randomMutator.names

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
    fname <- snippetStorage.findSourceFunc(branch)
    snippets = snippetStorage.getSnippets(fname)
    if snippets.nonEmpty
    targets = cov.targetCondViews.getOrElse(cond, Map()).getOrElse(view, Set())
  } yield {
    val results = for {
      snippet <- snippets
      t <- targets
      result <- mutate(code, t, snippet)
    } yield result
    val mutants = shuffle(results.toSeq).take(n)
    mutants ++ randomMutator(code, n - mutants.size, target)
  }).getOrElse(randomMutator(code, n, target))

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    randomMutator(ast, n, target)

  /** apply snippet to target */
  private def mutate(
    code: Code,
    target: Target,
    snippet: Snippet,
  ): Option[Result] = (code, target, snippet) match
    case (Code.Normal(str), t: Target.Normal, AstSnippet(ast)) =>
      val compatible = ast.chains.collectFirst {
        case syn: Syntactic if syn.name == t.prodName => syn
      }
      for {
        compatibleSnippet <- compatible
        mutatedAst <- Walker(t, compatibleSnippet)
          .walk(scriptParser.from(str))
          .headOption
      } yield {
        val mutant =
          Code.Normal(mutatedAst.toString(grammar = Some(cfg.grammar)))
        Result(name, mutant)
      }
    case (b: Code.Builtin, Target.BuiltinThis(thisArg), StrSnippet(str)) =>
      if (b.thisArg == Some(thisArg))
        Some(Result(name, b.replace(target, str)))
      else None
    case (b: Code.Builtin, Target.BuiltinArg(arg, i), StrSnippet(str)) =>
      if (b.args.lift(i) == Some(arg))
        Some(Result(name, b.replace(target, str)))
      else None
    case _ => None

  /** walker that replaces target AST with compatible snippet */
  class Walker(normalTarget: Target.Normal, replacement: Syntactic)
    extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      if (ast.matches(normalTarget))
        List(replacement)
      else super.walk(ast)
  }
}
