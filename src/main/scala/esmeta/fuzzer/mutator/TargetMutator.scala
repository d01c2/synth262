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
  import Mutator.*, Coverage.*, SpecStringSynthesizer.*, TargetMutator.*,
  CondTarget.*

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
    val mutationSite = choose(targets)
    val syn = ast.asInstanceOf[Syntactic]
    Walker(mutationSite, n).walk(syn)
  }).getOrElse(randomMutator(ast, n, target))

  /** internal walker for finding and mutating target */
  class Walker(target: Target, n: Int) extends Util.MultiplicativeListWalker {
    override def walk(ast: Syntactic): List[Syntactic] =
      if (ast.matches(target)) TotalWalker(ast, n)
      else
        val childMutations = super.walk(ast)
        if (childMutations.sizeIs != 1) // target found in subtree
          childMutations ++ callWrapVariants(ast)
        else childMutations

    /** .call(receiver, args) variants for unwrapped call expressions */
    private def callWrapVariants(ast: Syntactic): List[Syntactic] =
      if (ablation || !isUnwrappedCall(ast)) List()
      else
        for {
          prov <- provenance
          receiver <- provenanceGuided(ast, prov, into = None)
          wrapped <- wrapWithCall(
            ast,
            receiver.toString(grammar = Some(cfg.grammar)),
          )
        } yield wrapped
  }

  private def isUnwrappedCall(ast: Syntactic): Boolean =
    ast.name == "CoverCallExpressionAndAsyncArrowHead" &&
    ast.rhsIdx == 0 && !isCallWrapped(ast)

  /** per-node mutations (guided + blind) for a matched target subtree */
  object TotalWalker {
    def apply(ast: Syntactic, n: Int): List[Syntactic] =
      val nodes = enumerateNodes(ast)
      val k = Util.simpleAstCounter(ast)
      val c = (n - 1) / k + 1

      val guided: List[Syntactic] =
        if (ablation) List()
        else
          val perNode = provenance
            .flatMap { prov =>
              nodes.flatMap { site =>
                val injected = provenanceGuided(site, prov, into = Some(site))
                val mutations =
                  if (injected.nonEmpty) injected
                  else if (site eq ast) // into=None fallback only at root
                    provenanceGuided(ast, prov, into = None)
                  else List()
                mutations.flatMap(r => replaceSyntactic(ast, site, r))
              }
            }
          // .call() wrapping for unwrapped calls in the target subtree
          val callWraps = provenance.flatMap { prov =>
            nodes.flatMap { site =>
              if (!isUnwrappedCall(site)) List()
              else
                for {
                  receiver <- provenanceGuided(site, prov, into = None)
                  recStr = receiver.toString(grammar = Some(cfg.grammar))
                  wrapped <- wrapWithCall(site, recStr)
                  result <-
                    if (site eq ast) List(wrapped)
                    else replaceSyntactic(ast, site, wrapped).toList
                } yield result
            }
          }
          (perNode ++ callWraps).distinctBy(
            _.toString(grammar = Some(cfg.grammar)),
          )

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
    // template: { propDef }
    def injectPropRaw(propDef: String): List[Syntactic] =
      injectPropDef(propDef, ast.args, into)

    // template: { key: value }
    def injectProp(
      value: String,
      key: Option[String] = prov.propHint,
    ): List[Syntactic] = key match
      case Some(k) =>
        val propDef = s"$k : $value"
        val injected = injectPropRaw(propDef)
        if (injected.nonEmpty) injected
        else into.toList.flatMap(t => wrapAssign(t, propDef))
      case None => List()

    // template: { ... } (remove propHint)
    def ejectProp(): List[Syntactic] = for {
      target <- into.toList
      prop <- prov.propHint.toList
      result <- ejectPropDef(prop, target)
    } yield result

    // template: { get key() { throw 0; } }
    def injectThrowingGetter(
      key: Option[String] = prov.propHint,
    ): List[Syntactic] = key match
      case Some(k) =>
        val injected = injectPropRaw(s"get $k ( ) { throw 0 ; }")
        if (injected.nonEmpty) injected
        else
          into.toList.flatMap { t =>
            wrapDefineProperty(t, k, "get ( ) { throw 0 ; }")
          }
      case None => List()

    // template: { [Symbol.toPrimitive]: () => value }
    def injectToPrimitive(value: String): List[Syntactic] =
      val propDef = s"[Symbol.toPrimitive]: () => $value"
      val injected = injectPropRaw(propDef)
      if (injected.nonEmpty) injected
      else into.toList.flatMap { t => wrapAssign(t, propDef) }

    prov.chain match

      /** Property Reading Algorithms */
      // property existence: HasProperty
      case ("HasProperty", Normal(Some(true))) :: _  => injectProp("0")
      case ("HasProperty", Normal(Some(false))) :: _ => ejectProp()
      case ("HasProperty", Normal(None)) :: _        => injectProp("0")

      // property get: Get
      case ("Get", Normal(Some(true))) :: _  => injectProp("42")
      case ("Get", Normal(Some(false))) :: _ => ejectProp()
      case ("Get", Normal(None)) :: _        => injectProp("42")
      case ("Get", Abrupt) :: _ =>
        val fromGetter = injectThrowingGetter()
        if (fromGetter.nonEmpty) fromGetter
        else injectThrowingGetter(Some("0"))
      // callable value: IsCallable + Get chain
      case ("IsCallable", Normal(Some(true))) :: ("Get", Normal(_)) :: _ =>
        injectProp("() => {}")
      case ("IsCallable", Normal(Some(false))) :: ("Get", Normal(_)) :: _ =>
        injectProp("0")

      // callable value: GetMethod
      case ("GetMethod", Normal(Some(true))) :: _  => injectProp("() => {}")
      case ("GetMethod", Normal(Some(false))) :: _ => ejectProp()
      case ("GetMethod", Normal(None)) :: _        => injectProp("() => {}")
      case ("GetMethod", Abrupt) :: _              => injectProp("0")

      // iterator access: GetIteratorDirect
      case ("GetIteratorDirect", Normal(_)) :: _ =>
        injectProp("function ( ) { return { done : true } }", Some("next"))
      case ("GetIteratorDirect", Abrupt) :: _ =>
        injectThrowingGetter(Some("next"))

      // iterator step: IteratorStepValue
      case ("IteratorStepValue", Normal(_)) :: _ =>
        injectProp("function ( ) { return { done : true } }", Some("next"))
      case ("IteratorStepValue", Abrupt) :: _ =>
        injectProp("function ( ) { throw 0 ; }", Some("next"))

      /** Type Coercion Algorithms */
      // multi-step coercion via ToPrimitive (abrupt path)
      case ("ToString", Abrupt) :: ("ToPrimitive", _) :: _ =>
        injectToPrimitive("Symbol()")
      case ("ToNumber", Abrupt) :: ("ToPrimitive", _) :: _ =>
        injectToPrimitive("0n")

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
    ct: CondTarget,
    visited: Set[(Node, Local)] = Set(),
  ): List[List[(String, CallInst, CondTarget)]] =
    if (visited((node, target))) List()
    else {
      val newVisited = visited + ((node, target))
      val dataDep = cfg.depGraph.dataDeps(func)
      val defNodes =
        dataDep.useToDefs.getOrElse(node, Map()).getOrElse(target, Set())
      defNodes.toList.flatMap { n =>
        val callEntry: Option[(String, CallInst, CondTarget)] = n match
          case c: Call if c.callInst.lhs == target =>
            c.callInst match
              case ICall(_, EClo(name, _), _) =>
                Some((name, c.callInst, ct))
              case _ => None
          case _ => None
        val deeperChains = dataDep.uses(n).toList.flatMap { v =>
          findDefCall(func, n, v, ct, newVisited)
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
      val goal = !taken
      for {
        func <- cfg.funcOf.get(branch).toList
        dataDep = cfg.depGraph.dataDeps(func)
        condVar <- dataDep.uses(branch).toList
        ct <- condTarget(branch, condVar, goal).toList
        calls <- findDefCall(func, branch, condVar, ct)
        if calls.nonEmpty
      } yield
        val chain = calls.map((name, _, ct) => (name, ct))
        val propHint = calls.collectFirst {
          case (name, ICall(_, _, _ :: EStr(prop) :: _), _)
              if propReadingAlgos.contains(name) =>
            prop
        }
        Provenance(chain, propHint)
}

object TargetMutator {
  import esmeta.ir.{Func => IRFunc, *}

  /** condition target for the branch variable */
  enum CondTarget:
    case Abrupt
    case Normal(truthy: Option[Boolean]) // None = not yet determined

  case class Provenance(
    chain: List[(String, CondTarget)], // ordered nearest-to-branch
    propHint: Option[String], // property name from provenance chain
  )

  /** check if a ref contains the condition variable */
  private def isCondVar(ref: Ref, condVar: Local): Boolean = ref match
    case x: Local       => x == condVar
    case Field(base, _) => isCondVar(base, condVar)
    case _              => false

  /** resolve equality comparand to a CondTarget */
  private def resolveEq(comparand: Expr, goal: Boolean): Option[CondTarget] =
    comparand match
      case EBool(b) => Some(CondTarget.Normal(Some(goal == b)))
      case ENull()  => Some(CondTarget.Normal(Some(!goal)))
      case EUndef() => Some(CondTarget.Normal(Some(!goal)))
      case EEnum(_) => Some(CondTarget.Normal(Some(goal)))
      case _        => None

  /** determine what the condition variable needs to be */
  def condTarget(
    branch: Branch,
    condVar: Local,
    goal: Boolean,
  ): Option[CondTarget] =
    if (branch.isAbruptNode)
      Some(if (goal) CondTarget.Abrupt else CondTarget.Normal(None))
    else exprCondTarget(branch.cond, condVar, goal)

  private def exprCondTarget(
    expr: Expr,
    condVar: Local,
    goal: Boolean,
  ): Option[CondTarget] = expr match
    // compound abrupt check
    case EBinary(BOp.And, ETypeCheck(ERef(x: Local), ty), _)
        if x == condVar && ty.isCompletion =>
      Some(if (goal) CondTarget.Abrupt else CondTarget.Normal(None))
    // type check
    case ETypeCheck(ERef(ref), _) if isCondVar(ref, condVar) =>
      Some(CondTarget.Normal(Some(goal)))
    // existence check
    case EExists(ref) if isCondVar(ref, condVar) =>
      Some(CondTarget.Normal(Some(goal)))
    // equality
    case EBinary(BOp.Eq, ERef(ref), rhs) if isCondVar(ref, condVar) =>
      resolveEq(rhs, goal)
    case EBinary(BOp.Eq, lhs, ERef(ref)) if isCondVar(ref, condVar) =>
      resolveEq(lhs, goal)
    // bare variable as condition
    case ERef(ref) if isCondVar(ref, condVar) =>
      Some(CondTarget.Normal(Some(goal)))
    // negation
    case EUnary(UOp.Not, inner) =>
      exprCondTarget(inner, condVar, !goal)
    // conjunction / disjunction
    case EBinary(BOp.And, l, r) =>
      exprCondTarget(l, condVar, goal).orElse(exprCondTarget(r, condVar, goal))
    case EBinary(BOp.Or, l, r) =>
      exprCondTarget(l, condVar, goal).orElse(exprCondTarget(r, condVar, goal))
    case _ => None
}
