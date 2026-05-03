package esmeta.solver

import esmeta.ir.*
import esmeta.ty.ValueTy

// Solver terms
enum Term:
  case TVar(name: String)
  case TLit(value: LiteralExpr)
  case TField(base: Term, key: String)
  case TApp(name: Op | String, args: List[Term])
  case TList(elems: List[Term])
  case TRecord(tname: String, fields: Map[String, Term])
  case TMap(entries: List[(Term, Term)])
  case TTypeOf(t: Term)
  case TType(ty: ValueTy)

  def freeVars: Set[String] = this match
    case TVar(n)         => Set(n)
    case TLit(_)         => Set.empty
    case TField(base, _) => base.freeVars
    case TApp(_, args)   => args.flatMap(_.freeVars).toSet
    case TList(elems)    => elems.flatMap(_.freeVars).toSet
    case TRecord(_, fs)  => fs.values.flatMap(_.freeVars).toSet
    case TMap(es)        => es.flatMap((k, v) => k.freeVars ++ v.freeVars).toSet
    case TTypeOf(t)      => t.freeVars
    case TType(_)        => Set.empty

  def occurs(name: String): Boolean = freeVars.contains(name)

  override def toString: String = this match
    case TVar(n)         => n
    case TLit(v)         => v.toString
    case TField(base, k) => s"$base.$k"
    case TApp(n, args)   => s"$n(${args.mkString(", ")})"
    case TList(elems)    => s"[${elems.mkString(", ")}]"
    case TRecord(tn, fs) =>
      s"$tn{${fs.map((k, v) => s"$k: $v").mkString(", ")}}"
    case TMap(es)   => s"Map(${es.map((k, v) => s"$k -> $v").mkString(", ")})"
    case TTypeOf(t) => s"typeof($t)"
    case TType(ty)  => ty.toString

  def rewrite(target: Term, rep: Term): Term =
    if (this == target) rep
    else
      this match
        case TVar(_)         => this
        case TLit(_)         => this
        case TField(base, k) => TField(base.rewrite(target, rep), k)
        case TApp(op, args)  => TApp(op, args.map(_.rewrite(target, rep)))
        case TList(elems)    => TList(elems.map(_.rewrite(target, rep)))
        case TRecord(tn, fs) =>
          TRecord(tn, fs.map((k, v) => k -> v.rewrite(target, rep)))
        case TMap(es) =>
          TMap(
            es.map((k, v) => (k.rewrite(target, rep), v.rewrite(target, rep))),
          )
        case TTypeOf(t) => TTypeOf(t.rewrite(target, rep))
        case TType(_)   => this
