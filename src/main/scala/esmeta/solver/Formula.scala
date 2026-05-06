package esmeta.solver

enum Formula:
  case FNot(f: Formula)
  case FEq(lhs: SymExpr, rhs: SymExpr)
  case FLt(lhs: SymExpr, rhs: SymExpr)
  case FExists(base: SymExpr, field: SymExpr)

  def freeVars: Set[SymId] = this match
    case FNot(f)       => f.freeVars
    case FEq(l, r)     => l.freeVars ++ r.freeVars
    case FLt(l, r)     => l.freeVars ++ r.freeVars
    case FExists(b, k) => b.freeVars ++ k.freeVars

  override def toString: String = this match
    case FNot(f)       => s"!($f)"
    case FEq(l, r)     => s"($l = $r)"
    case FLt(l, r)     => s"($l < $r)"
    case FExists(b, k) => s"($b has $k)"

  def rewrite(target: SymExpr, rep: SymExpr): Formula = this match
    case FNot(f)   => FNot(f.rewrite(target, rep))
    case FEq(l, r) => FEq(l.rewrite(target, rep), r.rewrite(target, rep))
    case FLt(l, r) => FLt(l.rewrite(target, rep), r.rewrite(target, rep))
    case FExists(b, k) =>
      FExists(b.rewrite(target, rep), k.rewrite(target, rep))
