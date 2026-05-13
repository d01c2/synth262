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
    if (hasContradiction(norm)) None else Some(norm)

  private def normalize(f: Formula): Formula =
    f match
      // double negation elimination
      case FNot(FNot(inner)) => normalize(inner)
      // abrupt is not normal, and vice versa
      case FNot(FEq(SETypeOf(t), SEType(ty))) if ty <= NormalT =>
        FEq(SETypeOf(t), SEType(AbruptT))
      case FNot(FEq(SETypeOf(t), SEType(ty))) if ty <= AbruptT =>
        FEq(SETypeOf(t), SEType(NormalT))
      // boolean simplification
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
      // otherwise, identity
      case _ => f

  private def hasContradiction(fs: Goal): Boolean =
    val litBindings: Map[SymExpr, LiteralExpr] =
      fs.collect {
        case FEq(t, SELit(v)) => t -> v
        case FEq(SELit(v), t) => t -> v
      }.toMap
    val tyBindings: Map[SymExpr, List[ValueTy]] =
      fs.collect {
        case FEq(SETypeOf(t), SEType(ty)) if !(ty <= CompT) => (t, ty)
      }.groupMap(_._1)(_._2)
    fs.exists {
      // equality contradiction
      case FEq(SELit(a), SELit(b))   => a != b
      case FNot(FEq(l, r)) if l == r => true
      case FLt(l, r) if l == r       => true
      // t == v1 and t == v2 where v1 != v2
      case FEq(t, SELit(v)) => litBindings.get(t).exists(_ != v)
      case FEq(SELit(v), t) => litBindings.get(t).exists(_ != v)
      // t != v but t == v is already bound
      case FNot(FEq(t, SELit(v))) => litBindings.get(t).exists(_ == v)
      case FNot(FEq(SELit(v), t)) => litBindings.get(t).exists(_ == v)
      case _                      => false
    } || tyBindings.exists { (_, tys) =>
      // type contradiction
      tys.reduce(_ && _).isBottom
    }

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
}
