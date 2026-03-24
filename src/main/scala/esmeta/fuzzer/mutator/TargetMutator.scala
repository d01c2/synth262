package esmeta.fuzzer.mutator

import esmeta.cfg.CFG
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.synthesizer.*
import esmeta.util.BaseUtils.*

/** A target ECMAScript AST mutator */
class TargetMutator(ablation: Boolean = false)(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Mutator.*, Coverage.*, SpecStringSynthesizer.*

  val randomMutator = RandomMutator()

  val names = "TargetMutator" :: randomMutator.names

  val synthesizer = SpecStringSynthesizer(synBuilder(cfg.grammar))

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
  } yield {
    synthesizer.targetCond = Some(cond)
    val mutationCite = choose(targets)
    val syn = ast.asInstanceOf[Syntactic]
    Walker(mutationCite, n).walk(syn)
  }).getOrElse(randomMutator(ast, n, target))

  /** internal walker for finding and mutating target */
  class Walker(target: Target, n: Int) extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      if (ast.matches(target)) TotalWalker(ast, n)
      else super.walk(ast)
  }

  /** internal walker that mutates all internal nodes */
  object TotalWalker extends Util.AdditiveListWalker {
    private var c = 0
    private var priority: List[Syntactic] = List()

    // NOTE: prioritize condition aware mutants
    def apply(ast: Syntactic, n: Int): List[Syntactic] =
      val k = Util.simpleAstCounter(ast)
      c = (n - 1) / k + 1
      priority = List()
      val candidates = walk(ast) // blind mutants
      (shuffle(priority) ++ shuffle(candidates)).take(n).toList

    override def walk(ast: Syntactic): List[Syntactic] =
      val mutants = super.walk(ast)
      if (!ablation)
        for (prov <- synthesizer.provenance)
          priority = priority ++ provenanceGuided(ast, prov)
      val manual = shuffle(manuals(ast)).take(c).toList
      val synthesized = List.tabulate(c)(_ => synthesizer(ast))
      manual ++ synthesized ++ mutants
  }

  /** provenance guided mutation */
  private def provenanceGuided(
    ast: Syntactic,
    prov: Provenance,
  ): List[Syntactic] =
    def injectProp(value: String): List[Syntactic] =
      prov.propHint.toList.flatMap { prop =>
        synthesizer.injectProp(Some(prop), ast.args, Some(ast), value)
      }
    def ejectProp(): List[Syntactic] =
      prov.propHint.toList.flatMap { prop =>
        synthesizer.ejectProp(prop, ast.args, ast)
      }
    def injectGetter(value: String): List[Syntactic] =
      synthesizer.injectGetter(prov.propHint, ast.args, Some(ast), Some(value))
    def injectThrowingGetter(): List[Syntactic] =
      synthesizer.injectGetter(prov.propHint, ast.args, Some(ast), None)

    (prov.algoName, prov.side) match
      // Property existence: HasProperty
      case ("HasProperty", true)  => injectProp("0")
      case ("HasProperty", false) => ejectProp()

      // Abrupt: Get (getter throw)
      case ("Get", true) if prov.check.contains("Abrupt") =>
        injectThrowingGetter()
      case ("Get", false) if prov.check.contains("Abrupt") =>
        injectProp("0")
      // Abrupt: GetMethod (non-callable or getter throw)
      case ("GetMethod", true) if prov.check.contains("Abrupt") =>
        injectProp("0")
      case ("GetMethod", false) if prov.check.contains("Abrupt") =>
        injectProp("( ) => { }")

      // Callable value: Get+IsCallable
      case ("Get", true) if prov.check.contains("IsCallable") =>
        injectProp("( ) => { }")
      case ("Get", false) if prov.check.contains("IsCallable") =>
        injectProp("0")

      // Callable value: GetMethod (default)
      case ("GetMethod", true)  => injectProp("( ) => { }")
      case ("GetMethod", false) => ejectProp()

      // Property get: Get (default)
      case ("Get", true)  => injectProp("1")
      case ("Get", false) => ejectProp()

      // TODO: PropWritingAlgos
      // TODO: Type Coercion

      // others
      case _ => Nil
}
