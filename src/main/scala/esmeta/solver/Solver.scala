package esmeta.solver

import esmeta.ir.*
import esmeta.ty.*
import Formula.*, SymExpr.*

type Goal = List[Formula]
type Witness = Map[Sym, String]

object Solver {
  def solve(goal: Goal): Option[Goal] = simplify(rewrite(goal))

  def rewrite(goal: Goal): Goal =
    val next = goal.map(normalize).flatMap(RewriteRules.rewriteFormula)
    if (next == goal) goal.map(normalize) else rewrite(next)

  def simplify(formulas: Goal): Option[Goal] =
    val norm = removeTautologies(formulas)
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
    hasContradictionRaw(removeTautologies(rewrite(fs)))

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
        case FTypeCheck(t, ty) if !(ty <= CompT) => (t, ty)
      }.groupMap(_._1)(_._2)
    val negTyBindings: Map[SymExpr, List[ValueTy]] =
      fs.collect {
        case FNot(FTypeCheck(t, ty)) if !(ty <= CompT) => (t, ty)
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
