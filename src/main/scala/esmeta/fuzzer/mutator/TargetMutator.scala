package esmeta.fuzzer.mutator

import esmeta.es.*
import esmeta.fuzzer.synthesizer.*
import esmeta.es.util.*
import esmeta.es.util.Coverage.*
import esmeta.util.BaseUtils.*
import esmeta.cfg.CFG

/** A target ECMAScript AST mutator */
class TargetMutator(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Mutator.*, Code.*

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
      case Normal(str) =>
        val filtered = normalTargets.filter { nt =>
          scala.util.Try(str == nt.loc.getString(str)).toOption.getOrElse(false)
        } // FIXME: temporal patch for bug in localization
        if (filtered.nonEmpty) {
          val mutationCite = choose(filtered)
          scriptParser.from(str) match
            case syn: Syntactic =>
              Walker(mutationCite, n)
                .walk(syn)
                .map(_.toString(grammar = Some(cfg.grammar)))
                .map(str => Result(name, Normal(str)))
            case _ =>
              apply(str, n, target).map(str => Result(name, Normal(str)))
        } else apply(str, n, target).map(str => Result(name, Normal(str)))
      case builtin: Builtin =>
        val filtered = builtinTargets.filter { bt =>
          bt match
            case Target.BuiltinThis(thisArg) => builtin.thisArg == Some(thisArg)
            case Target.BuiltinArg(arg, i) => builtin.args.lift(i) == Some(arg)
            case _                         => false
        } // FIXME: temporal patch for bug in localization
        if (filtered.nonEmpty) {
          val mutationCite = choose(filtered)
          val argStr = mutationCite.argStr
          for {
            mutatedAst <- apply(argumentListParser.from(argStr), n, target)
            mutatedStr = mutatedAst.toString(grammar = Some(cfg.grammar))
            mutatedCode = builtin.replace(mutationCite, mutatedStr)
          } yield Result(name, mutatedCode)
        } else randomMutator(builtin, n, target)
  }).getOrElse(randomMutator(code, n, target))

  /** mutate ASTs */
  def apply(ast: Ast, n: Int, target: Option[(CondView, Coverage)]): Seq[Ast] =
    randomMutator(ast, n, target)

  /** internal walker for finding and mutating normal target */
  class Walker(normalTarget: Target.Normal, n: Int)
    extends Util.SingleListWalker {
    val Target.Normal(name, idx, subIdx, loc) = normalTarget
    def isTarget(ast: Syntactic): Boolean =
      ast.name == name && ast.rhsIdx == idx &&
      ast.subIdx == subIdx && ast.loc == Some(loc)
    def transform(ast: Syntactic): List[Syntactic] = TotalWalker(ast, n)
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
      List.tabulate(c)(_ => synthesizer(ast)) ++ mutants
  }
}
