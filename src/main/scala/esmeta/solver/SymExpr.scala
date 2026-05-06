package esmeta.solver

import esmeta.ir.*
import esmeta.ty.ValueTy

enum SymId:
  case This
  case Arg(index: Int)
  case NewTarget
  case Args

  override def toString: String = this match
    case This      => "#ThisArg"
    case Arg(k)    => s"#$k"
    case NewTarget => "#NewTarget"
    case Args      => "#Args"

enum SymExpr:
  case Sym(id: SymId)
  case Lit(value: LiteralExpr)
  case Proj(base: SymExpr, key: SymExpr)
  case App(name: Op | String, args: List[SymExpr])
  case SList(elems: List[SymExpr])
  case SRecord(tname: String, fields: Map[String, SymExpr])
  case SMap(entries: List[(SymExpr, SymExpr)])
  case TypeOf(t: SymExpr)
  case SType(ty: ValueTy)

  def freeVars: Set[SymId] = this match
    case Sym(id)        => Set(id)
    case Lit(_)         => Set.empty
    case Proj(base, k)  => base.freeVars ++ k.freeVars
    case App(_, args)   => args.flatMap(_.freeVars).toSet
    case SList(elems)   => elems.flatMap(_.freeVars).toSet
    case SRecord(_, fs) => fs.values.flatMap(_.freeVars).toSet
    case SMap(es)       => es.flatMap((k, v) => k.freeVars ++ v.freeVars).toSet
    case TypeOf(t)      => t.freeVars
    case SType(_)       => Set.empty

  def occurs(id: SymId): Boolean = freeVars.contains(id)

  override def toString: String = this match
    case Sym(id)       => id.toString
    case Lit(v)        => v.toString
    case Proj(base, k) => s"$base.$k"
    case App(n, args)  => s"$n(${args.mkString(", ")})"
    case SList(elems)  => s"[${elems.mkString(", ")}]"
    case SRecord(tn, fs) =>
      s"$tn{${fs.map((k, v) => s"$k: $v").mkString(", ")}}"
    case SMap(es)  => s"Map(${es.map((k, v) => s"$k -> $v").mkString(", ")})"
    case TypeOf(t) => s"typeof($t)"
    case SType(ty) => ty.toString

  def rewrite(target: SymExpr, rep: SymExpr): SymExpr =
    if (this == target) rep
    else
      this match
        case Sym(_) => this
        case Lit(_) => this
        case Proj(base, k) =>
          Proj(
            base.rewrite(target, rep),
            k.rewrite(target, rep),
          )
        case App(op, args) => App(op, args.map(_.rewrite(target, rep)))
        case SList(elems)  => SList(elems.map(_.rewrite(target, rep)))
        case SRecord(tn, fs) =>
          SRecord(tn, fs.map((k, v) => k -> v.rewrite(target, rep)))
        case SMap(es) =>
          SMap(es.map { (k, v) =>
            (k.rewrite(target, rep), v.rewrite(target, rep))
          })
        case TypeOf(t) => TypeOf(t.rewrite(target, rep))
        case SType(_)  => this
