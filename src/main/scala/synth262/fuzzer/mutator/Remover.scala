package synth262.fuzzer.mutator

import synth262.es.*
import synth262.es.util.*
import synth262.fuzzer.*
import synth262.util.BaseUtils.*
import synth262.fuzzer.synthesizer.{Synthesizer, RandomSynthesizer}
import synth262.cfg.CFG

/** A mutator that removes nodes of ECMAScript AST */
class Remover(using cfg: CFG)
  extends Mutator
  with Util.MultiplicativeListWalker {
  import Mutator.*, Remover.*, Coverage.*

  val randomMutator = RandomMutator()

  val names = "Remover" :: randomMutator.names

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    // count of removal candidates
    val k = victimCounter(ast)
    if (k > 0) {
      k1 = 0; k2 = k
      // if n is bigger than 2^k (the total size of the search space),
      // fill the remaining count with the randomly generated program.
      if (Math.pow(2, k) < n) {
        walk(ast) ++ randomMutator(ast, n - (1 << k), target)
      } else {
        // calculate the most efficient parameters
        // until 2^(k2 - 1) < n, increase k1 and decrease k2 (initially k)
        // if we have 5 victims and n is 4, k1 = 2, k2 = 3 after this loop.
        // k1: the number of survivors among victims
        // k2: the number of casualties among victims
        while (Math.pow(2, k2 - 1) >= n) { k1 += 1; k2 -= 1 }
        shuffle(walk(ast)).take(n)
      }
    } else randomMutator(ast, n, target)

  /** parameter for sampler */
  private var (k1, k2) = (0, 0)

  private def doDrop: Boolean =
    val prob: Float = k1.toFloat / (k1 + k2)
    if (k1 > 0 && randBool(prob)) { k1 -= 1; false }
    else if (k2 > 0) { k2 -= 1; true }
    else throw new Error("This is a bug in Remover")

  /** ast walker */
  override def walk(ast: Syntactic): List[Syntactic] =
    val mutants = super.walk(ast)
    val i = findSameChild(ast)
    if (i >= 0 && doDrop)
      mutants ++
      mutants.map(m => m.children(i).get.asInstanceOf[Syntactic])
    else mutants
}

object Remover {
  def findSameChild(ast: Ast): Int = ast match
    case Syntactic(name, args, rhsIdx, children) =>
      children.indexWhere { child =>
        child match
          case Some(Syntactic(`name`, `args`, _, _)) => true
          case _                                     => false
      }
    case _ => -1

  // count the number of asts that have same child
  val victimCounter = Util.AstCounter(ast => findSameChild(ast) >= 0)
}
