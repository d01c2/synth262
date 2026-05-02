package esmeta.solver

// Solver formulas
enum Formula:
  case FNot(f: Formula)
  case FEq(lhs: Term, rhs: Term)
  case FLt(lhs: Term, rhs: Term)
  case FExists(base: Term, field: String)

  def freeVars: Set[String] = this match
    case FNot(f)       => f.freeVars
    case FEq(l, r)     => l.freeVars ++ r.freeVars
    case FLt(l, r)     => l.freeVars ++ r.freeVars
    case FExists(b, _) => b.freeVars

  override def toString: String = this match
    case FNot(f)       => s"!($f)"
    case FEq(l, r)     => s"($l = $r)"
    case FLt(l, r)     => s"($l < $r)"
    case FExists(b, k) => s"""($b has "$k")"""

  def rewrite(target: Term, rep: Term): Formula = this match
    case FNot(f)       => FNot(f.rewrite(target, rep))
    case FEq(l, r)     => FEq(l.rewrite(target, rep), r.rewrite(target, rep))
    case FLt(l, r)     => FLt(l.rewrite(target, rep), r.rewrite(target, rep))
    case FExists(b, k) => FExists(b.rewrite(target, rep), k)
