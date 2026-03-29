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
              val intoSome = nodes.flatMap { site =>
                provenanceGuided(site, prov, into = Some(site)).flatMap { r =>
                  replaceSyntactic(ast, site, r)
                }
              }
              if (intoSome.nonEmpty) intoSome
              else
                nodes.flatMap { site =>
                  provenanceGuided(site, prov, into = None).flatMap { r =>
                    replaceSyntactic(ast, site, r)
                  }
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
    // template: { propDef }
    def injectPropRaw(propDef: String): List[Syntactic] =
      injectPropDef(propDef, ast.args, into)

    // template: { propHint: value }
    def injectProp(value: String): List[Syntactic] = prov.propHint match
      case Some(k) => injectPropRaw(s"$k : $value")
      case None    => List()

    // template: { ... } (remove propHint)
    def ejectProp(): List[Syntactic] = for {
      target <- into.toList
      prop <- prov.propHint.toList
      result <- ejectPropDef(prop, target)
    } yield result

    // template: { get propHint() { throw 0; } }
    def injectThrowingGetter(): List[Syntactic] = prov.propHint match
      case Some(k) => injectPropRaw(s"get $k ( ) { throw 0 ; }")
      case None    => List()

    // template: { [Symbol.toPrimitive]: () => value }
    def injectToPrimitive(value: String): List[Syntactic] =
      injectPropRaw(s"[Symbol.toPrimitive]: () => $value")

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
      case ("Get", Abrupt) :: _              => injectThrowingGetter()

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
