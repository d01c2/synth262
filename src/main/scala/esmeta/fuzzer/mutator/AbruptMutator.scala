package esmeta.fuzzer.mutator

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.es.util.Coverage.*
import esmeta.fuzzer.SnippetStorage
import esmeta.util.BaseUtils.*
import scala.util.Try

/** A mutator targeting abrupt completion branches */
class AbruptMutator(using cfg: CFG, snippetStorage: SnippetStorage)
  extends Mutator {
  import Mutator.*, Code.*

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
    if branch.isAbruptNode && !cond.cond // abrupt completion case
    funcName <- snippetStorage.findSourceFunc(cfg.funcOf(branch), branch)
    snippets = snippetStorage.getSnippets(funcName)
    if snippets.nonEmpty
    targets = cov.targetCondViews.getOrElse(cond, Map()).getOrElse(view, Set())
  } yield {
    val results = for {
      snippet <- snippets
      target <- targets
      result <- mutate(code, target, snippet)
    } yield result
    val taken = shuffle(results.toSeq).take(n)
    if (taken.size >= n) taken
    else taken ++ randomMutator(code, n - taken.size, target)
  }).getOrElse(randomMutator(code, n, target))

  /** mutate ASTs */
  def apply(ast: Ast, n: Int, target: Option[(CondView, Coverage)]): Seq[Ast] =
    randomMutator(ast, n, target)

  /** apply snippet to target */
  private def mutate(
    code: Code,
    target: Target,
    snippet: String,
  ): Option[Result] = (code, target) match
    case (Normal(str), t: Target.Normal) =>
      Walker(t, snippet).walk(scriptParser.from(str)).headOption.map { ast =>
        Result(name, Normal(ast.toString(grammar = Some(cfg.grammar))))
      }
    case (b: Builtin, _: Target.BuiltinThis | _: Target.BuiltinArg) =>
      Some(Result(name, b.replace(target, snippet)))
    case _ => None

  /** walker that replaces target AST with snippet */
  class Walker(target: Target.Normal, snippet: String)
    extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      val Target.Normal(n, idx, subIdx, loc) = target
      if (
        ast.name == n &&
        ast.rhsIdx == idx &&
        ast.subIdx == subIdx &&
        ast.loc == Some(loc)
      )
        Try(
          esParser(ast.name, ast.args).from(snippet).asInstanceOf[Syntactic],
        ).toOption.map(List(_)).getOrElse(super.walk(ast))
      else super.walk(ast)
  }
}
