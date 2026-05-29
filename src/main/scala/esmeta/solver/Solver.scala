package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

type Goal = List[Formula]
type Witness = Map[Sym, String]

object Solver {
  def solve(goal: Goal): Option[Goal] = solveAll(goal).headOption

  def solveAll(goal: Goal): LazyList[Goal] =
    val rewritten = rewrite(goal)
    val calls = modeledCalls(rewritten).toList.sortBy(_.toString)
    solveCases(rewritten, calls).flatMap { solved =>
      simplify(rewrite(solved))
        .map(stripCallFacts(_, calls.toSet))
        .to(LazyList)
    }

  def rewrite(goal: Goal): Goal =
    val next = goal
      .map(normalize)
      .flatMap(RewriteRules.rewriteFormula)
      .map(normalize)
      .distinct
    if (next == goal) next else rewrite(next)

  def simplify(formulas: Goal): Option[Goal] =
    val norm = removeTautologies(propagateEqualities(formulas))
    if (hasContradictionRaw(norm)) None else Some(norm)

  private def normalize(f: Formula): Formula =
    f match
      // double negation elimination
      case FNot(FNot(inner)) => normalize(inner)
      // abrupt is not normal, and vice versa
      case FNot(FEq(SETypeOf(t), SEType(ty))) =>
        normalize(FNot(FTypeCheck(t, ty)))
      case FNot(FTypeCheck(t, ty)) if ty <= NormalT => FTypeCheck(t, AbruptT)
      case FNot(FTypeCheck(t, ty)) if ty <= AbruptT => FTypeCheck(t, NormalT)
      // boolean simplification
      case FNot(FEq(l: SELit, r)) if !r.isInstanceOf[SELit] =>
        normalize(FNot(FEq(r, l)))
      case FNot(inner) => FNot(normalize(inner))
      case FEq(SEApp(UOp.Not, List(t)), SELit(EBool(b))) =>
        normalize(FEq(t, SELit(EBool(!b))))
      case FEq(SELit(EBool(b)), SEApp(UOp.Not, List(t))) =>
        normalize(FEq(t, SELit(EBool(!b))))
      case FEq(SEApp(BOp.Eq | BOp.Equal, List(l, r)), SELit(EBool(b))) =>
        if (b) FEq(l, r) else FNot(FEq(l, r))
      case FEq(SELit(EBool(b)), SEApp(BOp.Eq | BOp.Equal, List(l, r))) =>
        if (b) FEq(l, r) else FNot(FEq(l, r))
      case FEq(SEApp(BOp.Lt, List(l, r)), SELit(EBool(b))) =>
        if (b) FLt(l, r) else FNot(FLt(l, r))
      case FEq(SELit(EBool(b)), SEApp(BOp.Lt, List(l, r))) =>
        if (b) FLt(l, r) else FNot(FLt(l, r))
      case FEq(SETypeOf(t), SEType(ty)) => FTypeCheck(t, ty)
      case FEq(SEType(ty), SETypeOf(t)) => FTypeCheck(t, ty)
      // canonicalize equality before AO-specific rewrites
      case FEq(l: SELit, r) if !r.isInstanceOf[SELit] =>
        normalize(FEq(r, l))
      // otherwise, identity
      case _ => f

  def hasContradiction(fs: Goal): Boolean =
    simplify(rewrite(fs)).isEmpty

  private def modeledCalls(goal: Goal): Set[SymExpr] =
    collectExprs(goal, e => RewriteRules.isModeledCall(e))

  private def solveCases(
    base: Goal,
    calls: List[SymExpr],
  ): LazyList[Goal] =
    calls match
      case Nil => LazyList(base)
      case call :: rest =>
        val cases = RewriteRules.aoModel(call)
        if (cases.isEmpty) solveCases(base, rest)
        else
          LazyList.from(cases).flatMap { c =>
            simplify(rewrite(base ++ c.when ++ c.thenF)) match
              case None         => LazyList.empty
              case Some(solved) => solveCases(solved, rest)
          }

  private def stripCallFacts(goal: Goal, calls: Set[SymExpr]): Goal =
    goal.filterNot(f => calls.exists(existsExpr(f, _)))

  private def collectExprs(
    goal: Goal,
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
    case FNot(inner)      => exprsOf(inner)
    case FEq(l, r)        => List(l, r)
    case FLt(l, r)        => List(l, r)
    case FExists(b, k)    => List(b, k)
    case FTypeCheck(e, _) => List(e)

  private def children(e: SymExpr): List[SymExpr] = e match
    case SEField(base, _)    => List(base)
    case SEProj(base, k)     => List(base, k)
    case SEApp(_, args)      => args
    case SEList(es)          => es
    case SERecord(_, fields) => fields.values.toList
    case SEMap(entries)      => entries.flatMap((k, v) => List(k, v))
    case SETypeOf(t)         => List(t)
    case _                   => Nil

  private def propagateEqualities(fs: Goal): Goal =
    var facts = fs
    var seen = facts.toSet
    var changed = true

    def add(f: Formula): Unit =
      if (!seen(f)) {
        facts :+= f
        seen += f
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
      changed = false
      val litBindings: Map[SymExpr, LiteralExpr] =
        facts.collect {
          case FEq(t, SELit(v)) => t -> v
          case FEq(SELit(v), t) => t -> v
        }.toMap
      val negLitBindings: Map[SymExpr, Set[LiteralExpr]] =
        facts
          .collect {
            case FNot(FEq(t, SELit(v))) => t -> v
            case FNot(FEq(SELit(v), t)) => t -> v
          }
          .groupMap(_._1)(_._2)
          .view
          .mapValues(_.toSet)
          .toMap

      facts.foreach {
        case FEq(l, r) =>
          litBindings.get(l).foreach(v => add(FEq(r, SELit(v))))
          litBindings.get(r).foreach(v => add(FEq(l, SELit(v))))
          negLitBindings
            .getOrElse(l, Set.empty)
            .foreach(v => add(FNot(FEq(r, SELit(v)))))
          negLitBindings
            .getOrElse(r, Set.empty)
            .foreach(v => add(FNot(FEq(l, SELit(v)))))
          facts.foreach {
            case FLt(a, b) =>
              if (a == l) add(FLt(r, b))
              if (a == r) add(FLt(l, b))
              if (b == l) add(FLt(a, r))
              if (b == r) add(FLt(a, l))
            case FNot(FLt(a, b)) =>
              if (a == l) add(FNot(FLt(r, b)))
              if (a == r) add(FNot(FLt(l, b)))
              if (b == l) add(FNot(FLt(a, r)))
              if (b == r) add(FNot(FLt(a, l)))
            case FTypeCheck(t, ty) =>
              if (t == l) addType(r, ty, positive = true)
              if (t == r) addType(l, ty, positive = true)
            case FNot(FTypeCheck(t, ty)) =>
              if (t == l) addType(r, ty, positive = false)
              if (t == r) addType(l, ty, positive = false)
            case _ =>
          }
        case _ =>
      }
    }
    facts

  private def hasContradictionRaw(fs: Goal): Boolean =
    val eqSet = fs.collect { case f: FEq => f }.toSet
    val ltSet = fs.collect { case f: FLt => f }.toSet
    val litBindings: Map[SymExpr, LiteralExpr] =
      fs.collect {
        case FEq(t, SELit(v)) => t -> v
        case FEq(SELit(v), t) => t -> v
      }.toMap
    val tyBindings: Map[SymExpr, List[ValueTy]] =
      fs.collect {
        case FTypeCheck(t, ty) => (t, ty)
      }.groupMap(_._1)(_._2)
    val negTyBindings: Map[SymExpr, List[ValueTy]] =
      fs.collect {
        case FNot(FTypeCheck(t, ty)) => (t, ty)
      }.groupMap(_._1)(_._2)
    val literalTypeContradiction = litBindings.exists { (t, lit) =>
      val litTy = literalTy(lit)
      tyBindings.getOrElse(t, Nil).exists(ty => !(litTy <= ty)) ||
      negTyBindings.getOrElse(t, Nil).exists(ty => litTy <= ty)
    }
    fs.exists {
      // equality contradiction
      case FEq(SELit(a), SELit(b))   => a != b
      case FNot(FEq(l, r)) if l == r => true
      case FLt(l, r) if l == r       => true
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
      case FNot(f: FEq) => eqSet.contains(f)
      case FNot(f: FLt) => ltSet.contains(f)
      case _            => false
    } || tyBindings.exists { (_, tys) =>
      // type contradiction
      tys.reduce(_ && _).isBottom
    } || tyBindings.exists { (t, posTys) =>
      val posTy = posTys.reduce(_ && _)
      val negTy =
        negTyBindings.getOrElse(t, Nil).foldLeft(BotT: ValueTy)(_ || _)
      !negTy.isBottom && posTy <= negTy
    } || literalTypeContradiction

  private def removeTautologies(fs: Goal): Goal =
    val litBindings: Map[SymExpr, LiteralExpr] =
      fs.collect {
        case FEq(t, SELit(v)) => t -> v
        case FEq(SELit(v), t) => t -> v
      }.toMap
    fs.filterNot {
      // v = v is tautology
      case FEq(l, r) if l == r => true
      // t != v2 is redundant when t == v1
      case FNot(FEq(t, SELit(v))) => litBindings.get(t).exists(_ != v)
      case FNot(FEq(SELit(v), t)) => litBindings.get(t).exists(_ != v)
      case _                      => false
    }

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
