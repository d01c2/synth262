package synth262.fuzzer.mutator

import synth262.fuzzer.synthesizer.*
import synth262.es.*
import synth262.es.util.{Walker => AstWalker, *}
import synth262.fuzzer.*
import synth262.spec.Grammar
import synth262.util.*
import synth262.util.BaseUtils.*
import synth262.cfg.CFG

/** A mutator selects one of given mutators under weight */
class WeightedMutator(using cfg: CFG)(pairs: (Mutator, Int)*) extends Mutator {
  import Mutator.*, Coverage.*

  /** mutate code */
  override def apply(
    code: String,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Result] = weightedChoose(pairs)(code, n, target)

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] = weightedChoose(pairs)(ast, n, target)

  val names = pairs.toList.flatMap(_._1.names).sorted.distinct
}
