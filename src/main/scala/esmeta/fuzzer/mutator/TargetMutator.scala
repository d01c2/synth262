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
    def proxy(trap: String): Option[Syntactic] =
      synthesizer.wrapProxy(ast.args, trap, ast)
    def inject(
      propHint: Option[String],
      values: List[String] = defaultValues,
    ): Option[Syntactic] =
      propHint.flatMap(synthesizer.injectProp(_, ast.args, ast, values))
    def eject(propHint: Option[String]): Option[Syntactic] =
      propHint.flatMap(synthesizer.ejectProp(_, ast.args, ast))

    (prov.algoName, prov.side) match
      // Property existence: HasProperty / OrdinaryHasProperty
      case ("HasProperty" | "OrdinaryHasProperty", true) =>
        inject(prov.propHint).toList ++ proxy("has").toList
      case ("HasProperty" | "OrdinaryHasProperty", false) =>
        eject(prov.propHint).toList ++ proxy("has").toList

      // Own property existence: HasOwnProperty
      case ("HasOwnProperty", true) =>
        inject(prov.propHint).toList ++
        proxy("getOwnPropertyDescriptor").toList
      case ("HasOwnProperty", false) =>
        eject(prov.propHint).toList ++
        proxy("getOwnPropertyDescriptor").toList

      // Property get: Get / GetV / OrdinaryGet
      case ("Get" | "GetV" | "OrdinaryGet", true) =>
        val getter = synthesizer
          .injectGetter(ast.args, prov.propHint, Some(ast), truthyBodies)
          .toList
        inject(prov.propHint, truthyValues).toList ++
        getter ++ proxy("get").toList
      case ("Get" | "GetV" | "OrdinaryGet", false) =>
        eject(prov.propHint).toList ++ proxy("get").toList

      // Method get: GetMethod / Invoke (callable value)
      case ("GetMethod" | "Invoke", true) =>
        val method = synthesizer
          .injectMethod(ast.args, prov.propHint, Some(ast), truthyBodies)
          .toList
        method ++ proxy("get").toList
      case ("GetMethod" | "Invoke", false) =>
        val method = synthesizer
          .injectMethod(ast.args, prov.propHint, Some(ast), falsyBodies)
          .toList
        eject(prov.propHint).toList ++ method ++ proxy("get").toList

      // Property descriptor: OrdinaryGetOwnProperty
      case ("OrdinaryGetOwnProperty", true) =>
        inject(prov.propHint).toList ++
        proxy("getOwnPropertyDescriptor").toList
      case ("OrdinaryGetOwnProperty", false) =>
        eject(prov.propHint).toList ++
        proxy("getOwnPropertyDescriptor").toList

      // others
      case _ => Nil
}
