package esmeta.solver

import esmeta.ty.ValueTy

enum Formula:
  case FNot(f: Formula)
  case FImply(premise: List[Formula], conclusion: List[Formula])
  case FEq(lhs: SymExpr, rhs: SymExpr)
  case FLt(lhs: SymExpr, rhs: SymExpr)
  case FExists(base: SymExpr, field: SymExpr)
  case FTypeCheck(expr: SymExpr, ty: ValueTy)

  def freeVars: Set[Sym] = this match
    case FNot(f) => f.freeVars
    case FImply(premise, conclusion) =>
      (premise ++ conclusion).flatMap(_.freeVars).toSet
    case FEq(l, r)        => l.freeVars ++ r.freeVars
    case FLt(l, r)        => l.freeVars ++ r.freeVars
    case FExists(b, k)    => b.freeVars ++ k.freeVars
    case FTypeCheck(e, _) => e.freeVars

  override def toString: String = this match
    case FNot(f) => s"!($f)"
    case FImply(p, c) =>
      def conj(fs: List[Formula]): String =
        if (fs.isEmpty) "true" else fs.mkString(" /\\ ")
      s"((${conj(p)}) => (${conj(c)}))"
    case FEq(l, r)         => s"($l = $r)"
    case FLt(l, r)         => s"($l < $r)"
    case FExists(b, k)     => s"($b has $k)"
    case FTypeCheck(e, ty) => s"(? $e: $ty)"

  def rewrite(from: SymExpr, to: SymExpr): Formula = this match
    case FNot(f) => FNot(f.rewrite(from, to))
    case FImply(p, c) =>
      FImply(p.map(_.rewrite(from, to)), c.map(_.rewrite(from, to)))
    case FEq(l, r) => FEq(l.rewrite(from, to), r.rewrite(from, to))
    case FLt(l, r) => FLt(l.rewrite(from, to), r.rewrite(from, to))
    case FExists(b, k) =>
      FExists(b.rewrite(from, to), k.rewrite(from, to))
    case FTypeCheck(e, ty) => FTypeCheck(e.rewrite(from, to), ty)

case class AOCase(premise: List[Formula], conclusion: List[Formula])

object AOCase:
  def fromFormula(formula: Formula): Option[AOCase] = formula match
    case Formula.FImply(p, c) => Some(AOCase(p, c))
    case _                    => None

case class AOSummary(call: SymExpr, cases: List[AOCase])
