package esmeta.fuzzer.mutator

import esmeta.cfg.CFG
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.*
import esmeta.fuzzer.synthesizer.*
import esmeta.util.BaseUtils.*

/** A mutator that generates based on strings in spec literals */
class SpecStringMutator(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Mutator.*, SpecStringMutator.*, SpecStringSynthesizer.*, Coverage.*

  val randomMutator = RandomMutator()
  val synthesizer = SpecStringSynthesizer(synBuilder(cfg.grammar))

  val names = "SpecStringMutator" :: randomMutator.names

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    // count the number of primary expressions
    val k = primaryCounter(ast)
    if (k > 0) {
      synthesizer.targetBranch = None
      for ((condView, _) <- target)
        synthesizer.targetBranch = Some(condView.cond.branch)
      Seq.tabulate(n)(_ => walk(ast))
    } else randomMutator(ast, n, target)

  /** walk AST and return mutated AST */
  private def walk(ast: Ast): Ast = ast match
    case syn: Syntactic if isPrimary(syn) => synthesizer(syn)
    case Syntactic(name, args, rhsIdx, children) =>
      Syntactic(name, args, rhsIdx, children.map(_.map(walk)))
    case lex: Lexical => lex
}

object SpecStringMutator {
  val PRIMARY_EXPRESSION = "PrimaryExpression"

  def isPrimary(ast: Ast): Boolean = ast match
    case Syntactic(PRIMARY_EXPRESSION, _, _, _) => true
    case _                                      => false

  val primaryCounter = Util.AstCounter(isPrimary)
}
