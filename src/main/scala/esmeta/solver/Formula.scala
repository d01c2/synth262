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
    case FImply(premise, conclusion) =>
      def conj(fs: List[Formula]): String =
        if (fs.isEmpty) "true" else fs.mkString(" /\\ ")
      s"((${conj(premise)}) => (${conj(conclusion)}))"
    case FEq(l, r)         => s"($l = $r)"
    case FLt(l, r)         => s"($l < $r)"
    case FExists(b, k)     => s"($b has $k)"
    case FTypeCheck(e, ty) => s"(? $e: $ty)"

  def rewrite(target: SymExpr, rep: SymExpr): Formula = this match
    case FNot(f) => FNot(f.rewrite(target, rep))
    case FImply(premise, conclusion) =>
      FImply(
        premise.map(_.rewrite(target, rep)),
        conclusion.map(_.rewrite(target, rep)),
      )
    case FEq(l, r) => FEq(l.rewrite(target, rep), r.rewrite(target, rep))
    case FLt(l, r) => FLt(l.rewrite(target, rep), r.rewrite(target, rep))
    case FExists(b, k) =>
      FExists(b.rewrite(target, rep), k.rewrite(target, rep))
    case FTypeCheck(e, ty) => FTypeCheck(e.rewrite(target, rep), ty)
