package esmeta.solver

import esmeta.ir.*
import esmeta.ty.ValueTy

enum Sym:
  case This
  case NewTarget
  case ArgsList
  case Arg(index: Int)

  override def toString: String = this match
    case This      => "#this"
    case NewTarget => "#NewTarget"
    case ArgsList  => "#ArgumentsList"
    case Arg(k)    => s"#ArgumentsList[$k]"

enum SymExpr:
  case SESym(id: Sym)
  case SELit(value: LiteralExpr)
  case SEProj(base: SymExpr, key: SymExpr)
  case SEApp(name: Op | String, args: List[SymExpr])
  case SEList(elems: List[SymExpr])
  case SERecord(tname: String, fields: Map[String, SymExpr])
  case SEMap(entries: List[(SymExpr, SymExpr)])
  case SETypeOf(t: SymExpr)
  case SEType(ty: ValueTy)

  def freeVars: Set[Sym] = this match
    case SESym(id)       => Set(id)
    case SELit(_)        => Set.empty
    case SEProj(base, k) => base.freeVars ++ k.freeVars
    case SEApp(_, args)  => args.flatMap(_.freeVars).toSet
    case SEList(elems)   => elems.flatMap(_.freeVars).toSet
    case SERecord(_, fs) => fs.values.flatMap(_.freeVars).toSet
    case SEMap(es)       => es.flatMap((k, v) => k.freeVars ++ v.freeVars).toSet
    case SETypeOf(t)     => t.freeVars
    case SEType(_)       => Set.empty

  def occurs(id: Sym): Boolean = freeVars.contains(id)

  override def toString: String = this match
    case SESym(id)       => id.toString
    case SELit(v)        => v.toString
    case SEProj(base, k) => s"$base.$k"
    case SEApp(n, args)  => s"$n(${args.mkString(", ")})"
    case SEList(elems)   => s"[${elems.mkString(", ")}]"
    case SERecord(tn, fs) =>
      s"$tn{${fs.map((k, v) => s"$k: $v").mkString(", ")}}"
    case SEMap(es)   => s"Map(${es.map((k, v) => s"$k -> $v").mkString(", ")})"
    case SETypeOf(t) => s"typeof($t)"
    case SEType(ty)  => ty.toString

  def rewrite(target: SymExpr, rep: SymExpr): SymExpr =
    if (this == target) rep
    else
      this match
        case SESym(_) => this
        case SELit(_) => this
        case SEProj(base, k) =>
          SEProj(
            base.rewrite(target, rep),
            k.rewrite(target, rep),
          )
        case SEApp(op, args) => SEApp(op, args.map(_.rewrite(target, rep)))
        case SEList(elems)   => SEList(elems.map(_.rewrite(target, rep)))
        case SERecord(tn, fs) =>
          SERecord(tn, fs.map((k, v) => k -> v.rewrite(target, rep)))
        case SEMap(es) =>
          SEMap(es.map { (k, v) =>
            (k.rewrite(target, rep), v.rewrite(target, rep))
          })
        case SETypeOf(t) => SETypeOf(t.rewrite(target, rep))
        case SEType(_)   => this
