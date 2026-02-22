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

  /** synthesizer */
  val synthesizer = synBuilder(cfg.grammar)

  /** mutate code */
  def apply(
    code: Code,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Result] = (for {
    (cv, cov) <- target
    CondView(cond, view) = cv
    targets = cov.targetCondViews.getOrElse(cond, Map()).getOrElse(view, Set())
    normalTargets = targets.collect { case normal: Target.Normal => normal }
    builtinTargets = targets.collect {
      case builtinThis: Target.BuiltinThis => builtinThis
      case builtinArg: Target.BuiltinArg   => builtinArg
    }
  } yield {
    code match
      case Code.Normal(str) =>
        if (normalTargets.nonEmpty) {
          val mutationCite = choose(normalTargets)
          scriptParser.from(str) match
            case syn: Syntactic =>
              Walker(mutationCite, n)
                .walk(syn)
                .map { mutatedAst =>
                  val s = mutatedAst.toString(grammar = Some(cfg.grammar))
                  Result(name, Code.Normal(s))
                }
            case ast =>
              apply(ast, n, target).map { mutatedAst =>
                val s = mutatedAst.toString(grammar = Some(cfg.grammar))
                Result(name, Code.Normal(s))
              }
        } else
          val ast = scriptParser.from(str)
          apply(ast, n, target).map { mutatedAst =>
            val s = mutatedAst.toString(grammar = Some(cfg.grammar))
            Result(name, Code.Normal(s))
          }
      case builtin: Code.Builtin =>
        val filteredBuiltin = builtinTargets.filter { bt =>
          bt match
            case Target.BuiltinThis(thisArg) => builtin.thisArg == Some(thisArg)
            case Target.BuiltinArg(arg, i) => builtin.args.lift(i) == Some(arg)
            case _                         => false
        }.toSeq
        if (filteredBuiltin.nonEmpty)
          builtin.mutateTargets(filteredBuiltin, n, target)
        else if (normalTargets.nonEmpty) {
          val str = builtin.toString
          val mutationCite = choose(normalTargets)
          scriptParser.from(str) match
            case syn: Syntactic =>
              Walker(mutationCite, n)
                .walk(syn)
                .map { mutatedAst =>
                  val s = mutatedAst.toString(grammar = Some(cfg.grammar))
                  Result(name, Code.Normal(s))
                }
            case _ => randomMutator(builtin, n, target)
        } else randomMutator(builtin, n, target)
  }).getOrElse(randomMutator(code, n, target))

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    randomMutator(ast, n, target)

  /** internal walker for finding and mutating normal target */
  class Walker(normalTarget: Target.Normal, n: Int)
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
      List.tabulate(c) { _ => synthesizer(ast) } ++ mutants
  }
}
