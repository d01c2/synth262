package synth262.fuzzer.mutator

import synth262.cfg.CFG
import synth262.es.*
import synth262.es.util.*
import synth262.fuzzer.synthesizer.*
import synth262.util.BaseUtils.*

/** A nearest ECMAScript AST mutator */
class NearestMutator(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Coverage.*, Mutator.*

  val randomMutator = RandomMutator()

  val names = "NearestMutator" :: randomMutator.names

  /** synthesizers for localized replacements */
  val synthesizer = synBuilder(cfg.grammar)
  val specStringSynthesizer = SpecStringSynthesizer(synthesizer)

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] = (for {
    (condView, cov) <- target
    CondView(cond, view) = condView
    targets = cov.targetCondViews.getOrElse(cond, Map()).getOrElse(view, Set())
    if targets.nonEmpty
    nearest = choose(targets)
  } yield Walker(nearest, n).walk(ast))
    .getOrElse(randomMutator(ast, n, target))

  /** internal walker */
  class Walker(target: Target, n: Int) extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      if (ast.matches(target)) TotalWalker(ast, n)
      else super.walk(ast)
  }

  /** internal walker that mutates all internal nodes with same prob. */
  object TotalWalker extends Util.AdditiveListWalker {
    var c = 0
    def apply(ast: Syntactic, n: Int): List[Syntactic] =
      val k = Util.simpleAstCounter(ast)
      c = (n - 1) / k + 1
      shuffle(walk(ast)).take(n).toList

    override def walk(ast: Syntactic): List[Syntactic] =
      val mutants = super.walk(ast)
      val replacements =
        List.tabulate(c)(_ => synthesizer(ast)) ++
        List.tabulate(c)(_ => specStringSynthesizer(ast))
      replacements ++ mutants
  }
}
