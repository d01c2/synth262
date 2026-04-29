package esmeta.solver

import esmeta.ir.{BOp, UOp, VOp, LiteralExpr}
import esmeta.ty.ValueTy

// Solver terms
enum Term:
  case TVar(name: String)
  case TLit(value: LiteralExpr)
  case TField(base: Term, key: String)
  case TApp(name: String, args: List[Term])
  case TList(elems: List[Term])
  case TUOp(op: UOp, operand: Term)
  case TBOp(op: BOp, lhs: Term, rhs: Term)
  case TVOp(op: VOp, args: List[Term])
  case TSizeOf(t: Term)
  case TTypeOf(t: Term)
  case TType(ty: ValueTy)

  def freeVars: Set[String] = this match
    case TVar(n)           => Set(n)
    case TLit(_)           => Set.empty
    case TField(base, _)   => base.freeVars
    case TApp(_, args)     => args.flatMap(_.freeVars).toSet
    case TList(elems)      => elems.flatMap(_.freeVars).toSet
    case TUOp(_, t)        => t.freeVars
    case TBOp(_, lhs, rhs) => lhs.freeVars ++ rhs.freeVars
    case TVOp(_, args)     => args.flatMap(_.freeVars).toSet
    case TSizeOf(t)        => t.freeVars
    case TTypeOf(t)        => t.freeVars
    case TType(_)          => Set.empty

  def occurs(name: String): Boolean = freeVars.contains(name)

  def rewrite(target: Term, rep: Term): Term =
    if (this == target) rep
    else
      this match
        case TVar(_)         => this
        case TLit(_)         => this
        case TField(base, k) => TField(base.rewrite(target, rep), k)
        case TApp(op, args)  => TApp(op, args.map(_.rewrite(target, rep)))
        case TList(elems)    => TList(elems.map(_.rewrite(target, rep)))
        case TUOp(op, t)     => TUOp(op, t.rewrite(target, rep))
        case TBOp(op, l, r) =>
          TBOp(op, l.rewrite(target, rep), r.rewrite(target, rep))
        case TVOp(op, args) => TVOp(op, args.map(_.rewrite(target, rep)))
        case TSizeOf(t)     => TSizeOf(t.rewrite(target, rep))
        case TTypeOf(t)     => TTypeOf(t.rewrite(target, rep))
        case TType(_)       => this
