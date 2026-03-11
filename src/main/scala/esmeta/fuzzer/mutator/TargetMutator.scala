package esmeta.fuzzer.mutator

import esmeta.es.*
import esmeta.fuzzer.synthesizer.*
import esmeta.es.util.*
import esmeta.util.BaseUtils.*
import esmeta.cfg.CFG

/** A target ECMAScript AST mutator */
class TargetMutator(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Mutator.*, Coverage.*

  val randomMutator = RandomMutator()

  val names = "TargetMutator" :: randomMutator.names

  val specStringSynthesizer = SpecStringSynthesizer(synBuilder(cfg.grammar))

  /** mutate ASTs */
  def apply(ast: Ast, n: Int, target: Option[(CondView, Coverage)]): Seq[Ast] =
    (for {
      (condView, cov) <- target
      CondView(cond, view) = condView
      targets = cov.targetCondViews
        .getOrElse(cond, Map())
        .getOrElse(view, Set())
      if targets.nonEmpty
    } yield {
      specStringSynthesizer.targetBranch = Some(condView.cond.branch)

      val mutationCite = choose(targets)
      val syn = ast.asInstanceOf[Syntactic]
      Walker(mutationCite, n).walk(syn)
    }).getOrElse(randomMutator(ast, n, target))

  /** internal walker for finding and mutating target */
  class Walker(normalTarget: Target, n: Int)
    extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      if (ast.matches(normalTarget)) TotalWalker(ast, n)
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
      val cases = edgeCases(ast)
      val manual = if (cases.nonEmpty) List(choose(cases)) else Nil
      val synthesized = List.tabulate(c) { _ => specStringSynthesizer(ast) }
      manual ++ synthesized ++ mutants
  }
}
