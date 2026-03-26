package esmeta.fuzzer.mutator

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.synthesizer.{Util => _, *}
import esmeta.fuzzer.synthesizer.Util.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.util.BaseUtils.*

/** A target ECMAScript AST mutator */
class TargetMutator(ablation: Boolean = false)(using cfg: CFG)(
  val synBuilder: Synthesizer.Builder = RandomSynthesizer,
) extends Mutator {
  import Mutator.*, Coverage.*, SpecStringSynthesizer.*, TargetMutator.*

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
    targetCond = Some(cond)
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

  /** Generates all mutations for the target subtree */
  object TotalWalker {
    def apply(ast: Syntactic, n: Int): List[Syntactic] =
      val nodes = enumerateNodes(ast)
      val k = Util.simpleAstCounter(ast)
      val c = (n - 1) / k + 1

      // provenance-guided mutations (priority)
      val guided: List[Syntactic] =
        if (!ablation) {
          provenance
            .flatMap { prov =>
              nodes.flatMap { site =>
                val injected = provenanceGuided(site, prov, into = Some(site))
                val mutations =
                  if (injected.nonEmpty) injected
                  else provenanceGuided(site, prov, into = None)
                mutations.flatMap(r => replaceSyntactic(ast, site, r))
              }
            }
            .distinctBy(_.toString(grammar = Some(cfg.grammar)))
        } else List()

      // blind mutations (manual + synthesized per node)
      val blind: List[Syntactic] = nodes.flatMap { site =>
        val manual = shuffle(manuals(site)).take(c)
        val synthesized = List.tabulate(c)(_ => synthesizer(site))
        (manual ++ synthesized).flatMap(r => replaceSyntactic(ast, site, r))
      }

      (shuffle(guided) ++ shuffle(blind)).take(n).toList
  }

  /** provenance guided mutation */
  private def provenanceGuided(
    ast: Syntactic,
    prov: Provenance,
    into: Option[Syntactic], // where to inject (None = create new object)
  ): List[Syntactic] =
    /** mutation helpers */
    // template: { propHint: value }
    def injectProp(value: String): List[Syntactic] = prov.propHint match
      case Some(k) => injectPropDef(s"$k : $value", ast.args, into)
      case None    => List()

    // template: { ... } (no propHint)
    def ejectProp(): List[Syntactic] = for {
      target <- into.toList
      prop <- prov.propHint.toList
      result <- ejectPropDef(prop, target)
    } yield result

    // template: { get propHint() { throw 0; } }
    def injectThrowingGetter(): List[Syntactic] = prov.propHint match
      case Some(k) =>
        injectPropDef(s"get $k ( ) { throw 0 ; }", ast.args, into)
      case None => List()

    // template: { [Symbol.toPrimitive]: () => value }
    def injectToPrimitive(value: String): List[Syntactic] =
      injectPropDef(s"[Symbol.toPrimitive]: () => $value", ast.args, into)

    (prov.chain, prov.side) match

      /** Property Reading Algorithms */
      // Property existence: HasProperty
      case ("HasProperty" :: _, true)  => injectProp("0")
      case ("HasProperty" :: _, false) => ejectProp()

      // Abrupt: Get (getter throw)
      case ("Get" :: _, true) if prov.isAbrupt  => injectThrowingGetter()
      case ("Get" :: _, false) if prov.isAbrupt => injectProp("0")

      // Abrupt: GetMethod (non-callable or getter throw)
      case ("GetMethod" :: _, true) if prov.isAbrupt  => injectProp("0")
      case ("GetMethod" :: _, false) if prov.isAbrupt => injectProp("() => {}")

      // Callable value: IsCallable + Get chain
      case ("IsCallable" :: "Get" :: _, true)  => injectProp("() => {}")
      case ("IsCallable" :: "Get" :: _, false) => injectProp("0")

      // Callable value: GetMethod (default)
      case ("GetMethod" :: _, true)  => injectProp("() => {}")
      case ("GetMethod" :: _, false) => ejectProp()

      // Property get: Get (default)
      case ("Get" :: _, true)  => injectProp("0")
      case ("Get" :: _, false) => ejectProp()

      /** TODO: PropWritingAlgos */

      /** Type Coercion Algorithms */
      // Abrupt: ToString/ToNumber via ToPrimitive
      // e.g. { [Symbol.toPrimitive]: () => ... }
      case ("ToString" :: "ToPrimitive" :: _, true) if prov.isAbrupt =>
        injectToPrimitive("Symbol()")
      case ("ToString" :: "ToPrimitive" :: _, false) if prov.isAbrupt =>
        injectToPrimitive("0")
      case ("ToNumber" :: "ToPrimitive" :: _, true) if prov.isAbrupt =>
        injectToPrimitive("0n")
      case ("ToNumber" :: "ToPrimitive" :: _, false) if prov.isAbrupt =>
        injectToPrimitive("0")

      // others
      case _ => List()

  // ---------------------------------------------------------------------------
  // Provenance analysis
  // ---------------------------------------------------------------------------

  private var targetCond: Option[Cond] = None

  private def provenance: List[Provenance] =
    targetCond.toList.flatMap(findProvenance)

  /** trace def-use chain to find call chain from branch condition */
  private def findDefCall(
    func: Func,
    node: Node,
    target: Local,
    visited: Set[(Node, Local)] = Set(),
  ): List[List[(String, CallInst)]] =
    if (visited((node, target))) List()
    else {
      val newVisited = visited + ((node, target))
      val dataDep = cfg.depGraph.dataDeps(func)
      val defNodes =
        dataDep.useToDefs.getOrElse(node, Map()).getOrElse(target, Set())
      defNodes.toList.flatMap { n =>
        val callEntry: Option[(String, CallInst)] = n match
          case c: Call if c.callInst.lhs == target =>
            c.callInst match
              case ICall(_, EClo(name, _), _) => Some((name, c.callInst))
              case _                          => None
          case _ => None
        val deeperChains = dataDep.uses(n).toList.flatMap { v =>
          findDefCall(func, n, v, newVisited)
        }
        callEntry match
          case Some(entry) =>
            if (deeperChains.isEmpty) List(List(entry))
            else deeperChains.map(entry :: _)
          case None => deeperChains
      }
    }

  private def findProvenance(cond: Cond): List[Provenance] =
    val Cond(branch, taken) = cond
    if (findCondStr(branch.cond).isDefined) List()
    else
      for {
        func <- cfg.funcOf.get(branch).toList
        (condVar, takenSide) <- condRefVar(branch.cond, taken).toList
        calls <- findDefCall(func, branch, condVar)
        if calls.nonEmpty
      } yield
        val chain = calls.map(_._1)
        val propHint = calls.collectFirst {
          case (name, ICall(_, _, _ :: EStr(prop) :: _))
              if propReadingAlgos.contains(name) =>
            prop
        }
        Provenance(chain, propHint, !takenSide, branch.isAbruptNode)
}

object TargetMutator {
  import esmeta.ir.{Func => IRFunc, *}
  import esmeta.ty.AbruptT

  case class Provenance(
    chain: List[String], // ordered nearest-to-branch
    propHint: Option[String], // property name (property-reading only)
    side: Boolean,
    isAbrupt: Boolean = false, // whether branch is an abrupt check
  )

  def condRefVar(expr: Expr, cond: Boolean): Option[(Local, Boolean)] =
    expr match
      case EBinary(BOp.Eq, ERef(v: Local), EBool(b)) => Some((v, cond == b))
      case EBinary(BOp.Eq, EBool(b), ERef(v: Local)) => Some((v, cond == b))
      case EBinary(BOp.Eq, ERef(v: Local), EUndef()) => Some((v, !cond))
      case EBinary(BOp.Eq, EUndef(), ERef(v: Local)) => Some((v, !cond))
      case EBinary(BOp.Eq, ERef(v: Local), ENull())  => Some((v, !cond))
      case EBinary(BOp.Eq, ENull(), ERef(v: Local))  => Some((v, !cond))
      case EUnary(UOp.Not, inner)                    => condRefVar(inner, !cond)
      case EBinary(BOp.And, l, r) =>
        condRefVar(l, cond).orElse(condRefVar(r, cond))
      case EBinary(BOp.Or, l, r) =>
        condRefVar(l, cond).orElse(condRefVar(r, cond))
      case ETypeCheck(ERef(v: Local), ty) if ty.toValue == AbruptT =>
        Some((v, cond))
      case ERef(v: Local) => Some((v, cond))
      case _              => None
}
