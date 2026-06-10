package esmeta.solver

import esmeta.cfg.CFG
import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*
import java.util.concurrent.TimeoutException
import scala.collection.mutable

type Witness = Map[Sym, String]

class Solver(timeLimit: Option[Int] = None)(using CFG) {
  private lazy val startTime: Long = System.currentTimeMillis

  def timeout: Boolean =
    timeLimit.exists { limit =>
      val duration = System.currentTimeMillis - startTime
      duration >= limit.toLong * 1000L
    }

  def solve(goal: List[Formula]): Option[List[Formula]] =
    solveAll(goal).headOption

  def solveAll(goal: List[Formula]): LazyList[List[Formula]] =
    solveAllTraced(goal).map(_._2)

  /** like solveAll, but pairs each solution with its pre-strip form so
    * callers can observe what stripCallFacts dropped
    */
  def solveAllTraced(
    goal: List[Formula],
  ): LazyList[(List[Formula], List[Formula])] =
    if (timeout) throw TimeoutException("solver")
    val expanded = expand(goal)
    saturate(expanded).to(LazyList).flatMap { seed =>
      val initCalls = modeledCalls(seed)
      val calls = initCalls.toList.sortBy(_.toString)
      solveCases(seed, calls, initCalls).flatMap { (solved, allCalls) =>
        saturate(expand(solved))
          .map(solved => (solved, stripCallFacts(solved, allCalls)))
          .to(LazyList)
      }
    }

  def expand(goal: List[Formula]): List[Formula] =
    if (timeout) throw TimeoutException("solver")
    val next = goal.flatMap { formula =>
      RewriteRules.rewriteFormula(canonicalize(formula)).map(canonicalize)
    }.distinct
    if (next == goal) next else expand(next)

  def saturate(formulas: List[Formula]): Option[List[Formula]] =
    if (timeout) throw TimeoutException("solver")
    val saturated = closeFacts(formulas)
    if (hasContradictionRaw(saturated)) None else Some(saturated)

  private def canonicalize(f: Formula): Formula = f match
    case FImply(premise, conclusion) =>
      FImply(premise.map(canonicalize), conclusion.map(canonicalize))
    // double negation elimination
    case FNot(FNot(inner)) => canonicalize(inner)
    // abrupt is not normal, and vice versa
    case FNot(FEq(SETypeOf(t), SEType(ty))) =>
      canonicalize(FNot(FTypeCheck(t, ty)))
    case FNot(FTypeCheck(t, ty)) if ty <= NormalT => FTypeCheck(t, AbruptT)
    case FNot(FTypeCheck(t, ty)) if ty <= AbruptT => FTypeCheck(t, NormalT)
    // boolean simplification
    case FNot(FEq(l: SELit, r)) if !r.isInstanceOf[SELit] =>
      canonicalize(FNot(FEq(r, l)))
    case FNot(inner) => FNot(canonicalize(inner))
    case FEq(SEOp(UOp.Not, List(t)), SELit(EBool(b))) =>
      canonicalize(FEq(t, SELit(EBool(!b))))
    case FEq(SELit(EBool(b)), SEOp(UOp.Not, List(t))) =>
      canonicalize(FEq(t, SELit(EBool(!b))))
    case FEq(SEOp(BOp.Eq | BOp.Equal, List(l, r)), SELit(EBool(b))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(SELit(EBool(b)), SEOp(BOp.Eq | BOp.Equal, List(l, r))) =>
      if (b) FEq(l, r) else FNot(FEq(l, r))
    case FEq(SEOp(BOp.Lt, List(l, r)), SELit(EBool(b))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case FEq(SELit(EBool(b)), SEOp(BOp.Lt, List(l, r))) =>
      if (b) FLt(l, r) else FNot(FLt(l, r))
    case FEq(SETypeOf(t), SEType(ty)) => FTypeCheck(t, ty)
    case FEq(SEType(ty), SETypeOf(t)) => FTypeCheck(t, ty)
    // canonicalize equality before AO-specific rewrites
    case FEq(l: SELit, r) if !r.isInstanceOf[SELit] =>
      canonicalize(FEq(r, l))
    // otherwise, identity
    case _ => f

  def hasContradiction(fs: List[Formula]): Boolean =
    saturate(expand(fs)).isEmpty

  private def modeledCalls(goal: List[Formula]): Set[SymExpr] =
    collectExprs(goal, e => RewriteRules.isModeledCall(e))

  private def solveCases(
    base: List[Formula],
    calls: List[SymExpr],
    seen: Set[SymExpr],
  ): LazyList[(List[Formula], Set[SymExpr])] =
    if (timeout) throw TimeoutException("solver")
    calls match
      case Nil => LazyList((base, seen))
      case call :: rest =>
        val summary = RewriteRules.aoSummary(call)
        val cases = summary.cases
        if (cases.isEmpty) solveCases(base, rest, seen)
        else {
          LazyList.from(cases).flatMap { aoCase =>
            if (timeout) throw TimeoutException("solver")
            saturate(
              expand(base ++ aoCase.premise ++ aoCase.conclusion),
            ) match
              case None => LazyList.empty
              case Some(solved) =>
                val newCalls = modeledCalls(solved) -- seen
                val nextCalls = rest ++ newCalls.toList.sortBy(_.toString)
                solveCases(solved, nextCalls, seen ++ newCalls)
          }
        }

  // drop modeled-call facts, but first try to PROJECT them: substitute
  // modeled-call-rooted terms with equal call-free terms (the bridge
  // equalities are already in the saturated goal); a fact that becomes clean
  // survives for the reifier instead of being dropped.
  // [Z3] the strip interface itself disappears with the Z3 migration.
  private def stripCallFacts(
    goal: List[Formula],
    calls: Set[SymExpr],
  ): List[Formula] =
    val subst = directProjectionAliases(goal) ++ cleanAliases(goal, calls)
    goal.flatMap { f =>
      if (!containsAnyCall(f, calls)) Some(f)
      else
        f match
          case _: FImply => None // model axioms, not path facts
          case _ =>
            val g = mapFormula(f, substExpr(_, subst))
            val trivial = g match
              case FEq(l, r) => l == r
              case _         => false
            Option.when(!containsAnyCall(g, calls) && !trivial)(g)
    }.distinct

  // single-pass top-down substitution: replacements are call-free, so a
  // replaced node cannot contain further keys and recursion stops there
  private def substExpr(
    e: SymExpr,
    subst: Map[SymExpr, SymExpr],
  ): SymExpr =
    subst.get(e) match
      case Some(to) => to
      case None =>
        e match
          case SEField(base, key) =>
            SEField(substExpr(base, subst), substExpr(key, subst))
          case SEApp(op, args) => SEApp(op, args.map(substExpr(_, subst)))
          case SEClo(fname, captured) =>
            SEClo(fname, captured.map((k, v) => k -> substExpr(v, subst)))
          case SEList(elems) => SEList(elems.map(substExpr(_, subst)))
          case SERecord(tn, fs) =>
            SERecord(tn, fs.map((k, v) => k -> substExpr(v, subst)))
          case SEMap(es) =>
            SEMap(es.map((k, v) => (substExpr(k, subst), substExpr(v, subst))))
          case SETypeOf(t) => SETypeOf(substExpr(t, subst))
          case _           => e

  // [directProjection] coercions that consume their argument directly, so a
  // constraint on the RESULT soundly guides the ARGUMENT witness: identity-alias
  // `AO(arg)["Value"] -> arg` lets e.g. `ToIntegerOrInfinity(x) < 0` project to
  // `x < 0` and survive the call strip. Without it the bound is dropped and the
  // reifier defaults the argument (e.g. 0 on a `< 0` branch -> wrong side -> MISS).
  // An over-approximate projection only yields a MISS (verified downstream), never
  // an unsound cover. (LengthOfArrayLike is excluded: its argument is the object,
  // not the number, so identity projection would be wrong.)
  private val directProjectionAOs: Set[String] =
    Set("ToIntegerOrInfinity", "ToLength")

  // AO(arg)["Value"] -> arg for the whitelisted coercions
  private def directProjectionAliases(
    goal: List[Formula],
  ): Map[SymExpr, SymExpr] =
    collectExprs(
      goal,
      {
        case ValueField(SECall(ao, List(_))) => directProjectionAOs(ao)
        case _                               => false
      },
    ).collect {
      case e @ ValueField(SECall(_, List(arg))) => e -> arg
    }.toMap

  // modeled-call-rooted term -> equal call-free term, from goal equalities
  private def cleanAliases(
    goal: List[Formula],
    calls: Set[SymExpr],
  ): Map[SymExpr, SymExpr] =
    val pairs = goal.collect {
      case FEq(l, r)
          if containsCall(l, calls) && !containsCall(r, calls) =>
        l -> r
      case FEq(l, r)
          if containsCall(r, calls) && !containsCall(l, calls) =>
        r -> l
    }
    pairs.foldLeft(Map[SymExpr, SymExpr]()) {
      case (m, (k, v)) => if (m.contains(k)) m else m + (k -> v)
    }

  private def containsCall(e: SymExpr, calls: Set[SymExpr]): Boolean =
    calls.contains(e) || children(e).exists(containsCall(_, calls))

  private def mapFormula(f: Formula, m: SymExpr => SymExpr): Formula = f match
    case FNot(inner) => FNot(mapFormula(inner, m))
    case FImply(premise, conclusion) =>
      FImply(premise.map(mapFormula(_, m)), conclusion.map(mapFormula(_, m)))
    case FEq(l, r)         => FEq(m(l), m(r))
    case FLt(l, r)         => FLt(m(l), m(r))
    case FExists(b, k)     => FExists(m(b), m(k))
    case FTypeCheck(e, ty) => FTypeCheck(m(e), ty)

  private def containsAnyCall(
    formula: Formula,
    calls: Set[SymExpr],
  ): Boolean =
    calls.exists(existsExpr(formula, _))

  private def collectExprs(
    goal: List[Formula],
    pred: SymExpr => Boolean,
  ): Set[SymExpr] =
    def fromExpr(e: SymExpr): Set[SymExpr] =
      val self = if (pred(e)) Set(e) else Set.empty[SymExpr]
      self ++ children(e).flatMap(fromExpr)
    def fromFormula(f: Formula): Set[SymExpr] =
      exprsOf(f).flatMap(fromExpr).toSet
    goal.flatMap(fromFormula).toSet

  private def existsExpr(f: Formula, target: SymExpr): Boolean =
    def check(e: SymExpr): Boolean =
      e == target || children(e).exists(check)
    exprsOf(f).exists(check)

  private def exprsOf(f: Formula): List[SymExpr] = f match
    case FNot(inner) => exprsOf(inner)
    case FImply(premise, conclusion) =>
      (premise ++ conclusion).flatMap(exprsOf)
    case FEq(l, r)        => List(l, r)
    case FLt(l, r)        => List(l, r)
    case FExists(b, k)    => List(b, k)
    case FTypeCheck(e, _) => List(e)

  private def children(e: SymExpr): List[SymExpr] = e match
    case SEField(base, key)  => List(base, key)
    case SEApp(_, args)      => args
    case SEClo(_, captured)  => captured.values.toList
    case SEList(es)          => es
    case SERecord(_, fields) => fields.values.toList
    case SEMap(entries)      => entries.flatMap((k, v) => List(k, v))
    case SETypeOf(t)         => List(t)
    case _                   => Nil

  private def literalBindings(fs: List[Formula]): Map[SymExpr, LiteralExpr] =
    fs.collect {
      case FEq(t, SELit(v)) => t -> v
      case FEq(SELit(v), t) => t -> v
    }.toMap

  private def positiveTypeBindings(
    fs: List[Formula],
  ): Map[SymExpr, List[ValueTy]] =
    fs.collect {
      case FTypeCheck(t, ty) => t -> ty
    }.groupMap(_._1)(_._2)

  private def negativeTypeBindings(
    fs: List[Formula],
  ): Map[SymExpr, List[ValueTy]] =
    fs.collect {
      case FNot(FTypeCheck(t, ty)) => t -> ty
    }.groupMap(_._1)(_._2)

  private def propagateEqualities(
    fs: List[Formula],
  ): List[Formula] =
    val facts = mutable.ArrayBuffer.from(fs)
    val seen = mutable.HashSet.empty[Formula]
    fs.foreach { f =>
      if (timeout) throw TimeoutException("solver")
      seen += f
    }
    var changed = true

    def add(f: Formula): Unit =
      if (timeout) throw TimeoutException("solver")
      if (seen.add(f)) {
        facts += f
        changed = true
      }

    def addType(term: SymExpr, ty: ValueTy, positive: Boolean): Unit =
      term match
        case SELit(_) => ()
        case _ =>
          add(
            if (positive) FTypeCheck(term, ty) else FNot(FTypeCheck(term, ty)),
          )

    while (changed) {
      if (timeout) throw TimeoutException("solver")
      changed = false
      val currentFacts = facts.toList
      val litStructural = mutable.HashMap.empty[SymExpr, LiteralExpr]
      val litIdentity = java.util.IdentityHashMap[SymExpr, LiteralExpr]()
      val negLitStructural =
        mutable.HashMap.empty[SymExpr, mutable.HashSet[LiteralExpr]]
      val negLitIdentity =
        java.util.IdentityHashMap[SymExpr, mutable.HashSet[LiteralExpr]]()
      val structuralTargets =
        mutable.HashMap.empty[SymExpr, mutable.ArrayBuffer[Formula]]
      val identityTargets =
        java.util.IdentityHashMap[SymExpr, mutable.ArrayBuffer[Formula]]()

      def useStructuralIndex(term: SymExpr): Boolean =
        def loop(expr: SymExpr, budget: Int): Int =
          if (budget < 0) -1
          else
            expr match
              case SESym(_) | SEGlobal(_) | SELit(_) | SEType(_) =>
                budget - 1
              case SETypeOf(inner) =>
                loop(inner, budget - 1)
              case SEField(base, key) =>
                val next = loop(base, budget - 1)
                if (next < 0) -1 else loop(key, next)
              case SEApp(_, args) =>
                args.foldLeft(budget - 1) {
                  case (rest, _) if rest < 0 => -1
                  case (rest, arg)           => loop(arg, rest)
                }
              case SEClo(_, captured) =>
                captured.values.foldLeft(budget - 1) {
                  case (rest, _) if rest < 0 => -1
                  case (rest, v)             => loop(v, rest)
                }
              case SEList(elems) =>
                elems.foldLeft(budget - 1) {
                  case (rest, _) if rest < 0 => -1
                  case (rest, elem)          => loop(elem, rest)
                }
              case SERecord(_, fields) =>
                fields.values.foldLeft(budget - 1) {
                  case (rest, _) if rest < 0 => -1
                  case (rest, value)         => loop(value, rest)
                }
              case SEMap(entries) =>
                entries.foldLeft(budget - 1) {
                  case (rest, _) if rest < 0 => -1
                  case (rest, (key, value)) =>
                    val next = loop(key, rest)
                    if (next < 0) -1 else loop(value, next)
                }
        loop(term, 10) >= 0

      def identityBuffer[A](
        map: java.util.IdentityHashMap[SymExpr, mutable.ArrayBuffer[A]],
        term: SymExpr,
      ): mutable.ArrayBuffer[A] =
        val found = map.get(term)
        if (found != null) found
        else {
          val created = mutable.ArrayBuffer.empty[A]
          map.put(term, created)
          created
        }

      def identitySet[A](
        map: java.util.IdentityHashMap[SymExpr, mutable.HashSet[A]],
        term: SymExpr,
      ): mutable.HashSet[A] =
        val found = map.get(term)
        if (found != null) found
        else {
          val created = mutable.HashSet.empty[A]
          map.put(term, created)
          created
        }

      def putLit(term: SymExpr, value: LiteralExpr): Unit =
        if (useStructuralIndex(term)) litStructural(term) = value
        else litIdentity.put(term, value)

      def getLit(term: SymExpr): Option[LiteralExpr] =
        if (useStructuralIndex(term)) litStructural.get(term)
        else Option(litIdentity.get(term))

      def putNegLit(term: SymExpr, value: LiteralExpr): Unit =
        if (useStructuralIndex(term))
          negLitStructural
            .getOrElseUpdate(term, mutable.HashSet.empty)
            .add(value)
        else identitySet(negLitIdentity, term).add(value)

      def getNegLits(term: SymExpr): Iterable[LiteralExpr] =
        if (useStructuralIndex(term))
          negLitStructural.getOrElse(term, Set.empty)
        else Option(negLitIdentity.get(term)).getOrElse(Set.empty)

      def index(term: SymExpr, fact: Formula): Unit =
        if (useStructuralIndex(term))
          structuralTargets
            .getOrElseUpdate(term, mutable.ArrayBuffer.empty)
            .append(fact)
        else identityBuffer(identityTargets, term).append(fact)

      currentFacts.foreach {
        case FEq(t, SELit(v)) =>
          putLit(t, v)
        case FEq(SELit(v), t) =>
          putLit(t, v)
        case FNot(FEq(t, SELit(v))) =>
          putNegLit(t, v)
        case FNot(FEq(SELit(v), t)) =>
          putNegLit(t, v)
        case fact @ FLt(a, b) =>
          index(a, fact); index(b, fact)
        case fact @ FNot(FLt(a, b)) =>
          index(a, fact); index(b, fact)
        case fact @ FTypeCheck(t, _) =>
          index(t, fact)
        case fact @ FNot(FTypeCheck(t, _)) =>
          index(t, fact)
        case _ =>
      }

      def replaceTerm(expr: SymExpr, from: SymExpr, to: SymExpr): SymExpr =
        if (expr == from) to else expr

      def addSubstituted(fact: Formula, from: SymExpr, to: SymExpr): Unit =
        fact match
          case FLt(a, b) =>
            add(FLt(replaceTerm(a, from, to), replaceTerm(b, from, to)))
          case FNot(FLt(a, b)) =>
            add(
              FNot(
                FLt(replaceTerm(a, from, to), replaceTerm(b, from, to)),
              ),
            )
          case FTypeCheck(t, ty) =>
            addType(replaceTerm(t, from, to), ty, positive = true)
          case FNot(FTypeCheck(t, ty)) =>
            addType(replaceTerm(t, from, to), ty, positive = false)
          case _ =>

      def propagateSubstitution(from: SymExpr, to: SymExpr): Unit =
        val targets =
          if (useStructuralIndex(from)) structuralTargets.get(from)
          else Option(identityTargets.get(from))
        targets.foreach {
          _.foreach { fact =>
            if (timeout) throw TimeoutException("solver")
            addSubstituted(fact, from, to)
          }
        }

      currentFacts.foreach { formula =>
        if (timeout) throw TimeoutException("solver")
        formula match
          case FEq(l, r) =>
            getLit(l).foreach(v => add(FEq(r, SELit(v))))
            getLit(r).foreach(v => add(FEq(l, SELit(v))))
            getNegLits(l).foreach(v => add(FNot(FEq(r, SELit(v)))))
            getNegLits(r).foreach(v => add(FNot(FEq(l, SELit(v)))))
            propagateSubstitution(l, r)
            propagateSubstitution(r, l)
          case _ =>
      }
    }
    facts.toList

  private def closeFacts(
    formulas: List[Formula],
  ): List[Formula] =
    var facts = formulas.distinct
    var changed = true
    while (changed) {
      if (timeout) throw TimeoutException("solver")
      val next =
        removeTautologies(
          propagateEqualities(dischargeImplications(facts)),
        ).distinct
      changed = next != facts
      facts = next
    }
    facts

  private def dischargeImplications(fs: List[Formula]): List[Formula] =
    val known = fs.toSet
    val implied = fs.collect {
      case FImply(premise, conclusion) if premise.forall(known) =>
        conclusion
    }.flatten
    fs ++ implied.filterNot(known)

  private def hasContradictionRaw(fs: List[Formula]): Boolean =
    val eqSet = fs.collect { case f: FEq => f }.toSet
    val ltSet = fs.collect { case f: FLt => f }.toSet
    val existsSet = fs.collect { case f: FExists => f }.toSet
    val litBindings = literalBindings(fs)
    val tyBindings = positiveTypeBindings(fs)
    val negTyBindings = negativeTypeBindings(fs)
    val literalTypeContradiction = litBindings.exists { (t, lit) =>
      val litTy = literalTy(lit)
      tyBindings.getOrElse(t, Nil).exists(ty => !(litTy <= ty)) ||
      negTyBindings.getOrElse(t, Nil).exists(ty => litTy <= ty)
    }
    fs.exists {
      // equality contradiction
      case FEq(SELit(a), SELit(b))       => a != b
      case FNot(FEq(l, r)) if l == r     => true
      case FLt(l, r) if l == r           => true
      case FLt(SELit(a), SELit(b))       => literalLt(a, b).contains(false)
      case FNot(FLt(SELit(a), SELit(b))) => literalLt(a, b).contains(true)
      // literal/type contradiction
      case FTypeCheck(SELit(v), ty)       => !(literalTy(v) <= ty)
      case FNot(FTypeCheck(SELit(v), ty)) => literalTy(v) <= ty
      // t == v1 and t == v2 where v1 != v2
      case FEq(t, SELit(v)) => litBindings.get(t).exists(_ != v)
      case FEq(SELit(v), t) => litBindings.get(t).exists(_ != v)
      // t != v but t == v is already bound
      case FNot(FEq(t, SELit(v))) => litBindings.get(t).exists(_ == v)
      case FNot(FEq(SELit(v), t)) => litBindings.get(t).exists(_ == v)
      // direct positive/negative contradiction
      case FNot(f: FEq)     => eqSet.contains(f)
      case FNot(f: FLt)     => ltSet.contains(f)
      case FNot(f: FExists) => existsSet.contains(f)
      case _                => false
    } || tyBindings.exists { (_, tys) =>
      // type contradiction
      tys.reduce(_ && _).isBottom
    } || tyBindings.exists { (t, posTys) =>
      val posTy = posTys.reduce(_ && _)
      val negTy =
        negTyBindings.getOrElse(t, Nil).foldLeft(BotT: ValueTy)(_ || _)
      !negTy.isBottom && posTy <= negTy
    } || literalTypeContradiction

  private def removeTautologies(fs: List[Formula]): List[Formula] =
    val litBindings = literalBindings(fs)
    fs.filterNot {
      // v = v is tautology
      case FEq(l, r) if l == r => true
      case FLt(SELit(a), SELit(b)) =>
        literalLt(a, b).contains(true)
      case FNot(FLt(SELit(a), SELit(b))) =>
        literalLt(a, b).contains(false)
      // t != v2 is redundant when t == v1
      case FNot(FEq(t, SELit(v))) => litBindings.get(t).exists(_ != v)
      case FNot(FEq(SELit(v), t)) => litBindings.get(t).exists(_ != v)
      case _                      => false
    }

  private def literalLt(
    lhs: LiteralExpr,
    rhs: LiteralExpr,
  ): Option[Boolean] =
    (lhs, rhs) match
      case (ENumber(d), _) if d.isNaN => Some(false)
      case (_, ENumber(d)) if d.isNaN => Some(false)
      case _ =>
        (numericOrder(lhs), numericOrder(rhs)) match
          case (Some((lRank, l)), Some((rRank, r))) =>
            Some(if (lRank == rRank) lRank == 0 && l < r else lRank < rRank)
          case _ => None

  private def numericOrder(
    lit: LiteralExpr,
  ): Option[(Int, BigDecimal)] = lit match
    case EMath(n)                      => Some(0 -> n)
    case ENumber(d) if d.isPosInfinity => Some(1 -> BigDecimal(0))
    case ENumber(d) if d.isNegInfinity => Some(-1 -> BigDecimal(0))
    case ENumber(d) if !d.isNaN        => Some(0 -> BigDecimal(d))
    case EInfinity(true)               => Some(1 -> BigDecimal(0))
    case EInfinity(false)              => Some(-1 -> BigDecimal(0))
    case _                             => None

  private def literalTy(lit: LiteralExpr): ValueTy = lit match
    case EMath(n)     => MathT(n)
    case EInfinity(p) => InfinityT(p)
    case ENumber(n)   => NumberT(esmeta.state.Number(n))
    case EBigInt(_)   => BigIntT
    case EStr(s)      => StrT(s)
    case EBool(b)     => BoolT(b)
    case EUndef()     => UndefT
    case ENull()      => NullT
    case EEnum(name)  => EnumT(name)
    case ECodeUnit(_) => CodeUnitT
}

object Solver {
  def apply(timeLimit: Option[Int] = None)(using CFG): Solver =
    new Solver(timeLimit)

  // apps the solve+reify pipeline understands: MOP internal methods + a few AOs
  private val internalMethodApps: Set[String] = Set(
    "Call",
    "Construct",
    "GetPrototypeOf",
    "SetPrototypeOf",
    "IsExtensible",
    "PreventExtensions",
    "OwnPropertyKeys",
    "Set",
    "HasProperty",
    "DefineOwnProperty",
    "Delete",
    "GetOwnProperty",
  )
  private val reifiableAOs: Set[String] =
    Set("LengthOfArrayLike", "ToLength", "ToIntegerOrInfinity")
  private def isKnownApp(name: String): Boolean =
    internalMethodApps.contains(name) || reifiableAOs.contains(name)

  // a goal mentions an application the pipeline cannot interpret
  def hasUninterpretableApp(fs: List[Formula]): Boolean =
    def fromExpr(t: SymExpr): Set[String] = t match
      case SECall(fname, args)    => Set(fname) ++ args.flatMap(fromExpr)
      case SEResidual(name, args) => Set(name) ++ args.flatMap(fromExpr)
      case SEApp(_, args)         => args.flatMap(fromExpr).toSet
      case SEGlobal(_)            => Set()
      case SEField(base, key)     => fromExpr(base) ++ fromExpr(key)
      case SEList(elems)          => elems.flatMap(fromExpr).toSet
      case SERecord(_, fs)        => fs.values.flatMap(fromExpr).toSet
      case SEMap(es)   => es.flatMap((k, v) => fromExpr(k) ++ fromExpr(v)).toSet
      case SETypeOf(t) => fromExpr(t)
      case _           => Set()
    def fromFormula(f: Formula): Set[String] = f match
      case FNot(inner) => fromFormula(inner)
      case FImply(premise, conclusion) =>
        (premise ++ conclusion).flatMap(fromFormula).toSet
      case FEq(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FLt(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FExists(b, _)    => fromExpr(b)
      case FTypeCheck(e, _) => fromExpr(e)
    fs.exists(fromFormula(_).exists(!isKnownApp(_)))

  // names of the outermost uninterpretable applications in a formula
  def outerAppNames(f: Formula): Set[String] =
    def fromExpr(t: SymExpr): Set[String] = t match
      case SECall(fname, _) if !isKnownApp(fname) => Set(fname)
      case SEResidual(name, _)                    => Set(name)
      case SEApp(_, args)     => args.flatMap(fromExpr).toSet
      case SEGlobal(_)        => Set()
      case SEField(base, key) => fromExpr(base) ++ fromExpr(key)
      case SEList(elems)      => elems.flatMap(fromExpr).toSet
      case SERecord(_, fs)    => fs.values.flatMap(fromExpr).toSet
      case SEMap(es)   => es.flatMap((k, v) => fromExpr(k) ++ fromExpr(v)).toSet
      case SETypeOf(t) => fromExpr(t)
      case _           => Set()
    f match
      case FNot(inner) => outerAppNames(inner)
      case FImply(premise, conclusion) =>
        (premise ++ conclusion).flatMap(outerAppNames).toSet
      case FEq(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FLt(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FExists(b, _)    => fromExpr(b)
      case FTypeCheck(e, _) => fromExpr(e)
}
