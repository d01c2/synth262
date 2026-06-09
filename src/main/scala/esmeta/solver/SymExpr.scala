package esmeta.solver

import esmeta.ir.{Op as CoreOp, *}
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

enum AppKind:
  case Op(op: CoreOp)
  case Residual(name: String)
  case Call(name: String)

  override def toString: String = this match
    case Op(op)         => op.toString
    case Residual(name) => s"residual:$name"
    case Call(name)     => name

enum SymExpr:
  case SESym(id: Sym)
  case SEGlobal(name: String)
  case SELit(value: LiteralExpr)
  case SEField(base: SymExpr, key: SymExpr)
  case SEApp(kind: AppKind, args: List[SymExpr])
  case SEClo(fname: String, captured: Map[Name, SymExpr])
  case SEList(elems: List[SymExpr])
  case SERecord(tname: String, fields: Map[String, SymExpr])
  case SEMap(entries: List[(SymExpr, SymExpr)])
  case SETypeOf(t: SymExpr)
  case SEType(ty: ValueTy)

  def freeVars: Set[Sym] = this match
    case SESym(id)          => Set(id)
    case SEGlobal(_)        => Set.empty
    case SELit(_)           => Set.empty
    case SEField(base, key) => base.freeVars ++ key.freeVars
    case SEApp(_, args)     => args.flatMap(_.freeVars).toSet
    case SEClo(_, captured) => captured.values.flatMap(_.freeVars).toSet
    case SEList(elems)      => elems.flatMap(_.freeVars).toSet
    case SERecord(_, fs)    => fs.values.flatMap(_.freeVars).toSet
    case SEMap(es)   => es.flatMap((k, v) => k.freeVars ++ v.freeVars).toSet
    case SETypeOf(t) => t.freeVars
    case SEType(_)   => Set.empty

  def occurs(id: Sym): Boolean = freeVars.contains(id)

  override def toString: String = this match
    case SESym(id)          => id.toString
    case SEGlobal(name)     => s"@$name"
    case SELit(v)           => v.toString
    case SEField(base, key) => s"$base[$key]"
    case SEApp(n, args)     => s"$n(${args.mkString(", ")})"
    case SEClo(fname, captured) =>
      s"clo<$fname>{${captured.map((k, v) => s"$k=$v").mkString(", ")}}"
    case SEList(elems)      => s"[${elems.mkString(", ")}]"
    case SERecord(tn, fs) =>
      s"$tn{${fs.map((k, v) => s"$k: $v").mkString(", ")}}"
    case SEMap(es)   => s"Map(${es.map((k, v) => s"$k -> $v").mkString(", ")})"
    case SETypeOf(t) => s"typeof($t)"
    case SEType(ty)  => ty.toString

  def rewrite(from: SymExpr, to: SymExpr): SymExpr =
    if (this == from) to
    else
      this match
        case SESym(_)    => this
        case SEGlobal(_) => this
        case SELit(_)    => this
        case SEField(base, key) =>
          SEField(base.rewrite(from, to), key.rewrite(from, to))
        case SEApp(op, args) => SEApp(op, args.map(_.rewrite(from, to)))
        case SEClo(fname, captured) =>
          SEClo(fname, captured.map((k, v) => k -> v.rewrite(from, to)))
        case SEList(elems)   => SEList(elems.map(_.rewrite(from, to)))
        case SERecord(tn, fs) =>
          SERecord(tn, fs.map((k, v) => k -> v.rewrite(from, to)))
        case SEMap(es) =>
          SEMap(es.map((k, v) => (k.rewrite(from, to), v.rewrite(from, to))))
        case SETypeOf(t) => SETypeOf(t.rewrite(from, to))
        case SEType(_)   => this

object SymExpr:
  def SEField(base: SymExpr, field: String): SymExpr =
    SEField(base, SELit(EStr(field)))

  object SEOp:
    def apply(op: CoreOp, args: List[SymExpr]): SymExpr =
      SEApp(AppKind.Op(op), args)

    def unapply(expr: SymExpr): Option[(CoreOp, List[SymExpr])] = expr match
      case SEApp(AppKind.Op(op), args) => Some(op -> args)
      case _                           => None

  object SEResidual:
    def apply(name: String, args: List[SymExpr]): SymExpr =
      SEApp(AppKind.Residual(name), args)

    def unapply(expr: SymExpr): Option[(String, List[SymExpr])] = expr match
      case SEApp(AppKind.Residual(name), args) => Some(name -> args)
      case _                                   => None

  object SECall:
    def apply(name: String, args: List[SymExpr]): SymExpr =
      SEApp(AppKind.Call(name), args)

    def unapply(expr: SymExpr): Option[(String, List[SymExpr])] = expr match
      case SEApp(AppKind.Call(name), args) => Some(name -> args)
      case _                               => None

  object StaticField:
    def unapply(expr: SymExpr): Option[(SymExpr, String)] = expr match
      case SEField(base, SELit(EStr(field))) => Some(base -> field)
      case _                                 => None

  object ValueField:
    def unapply(expr: SymExpr): Option[SymExpr] = expr match
      case StaticField(base, "Value") => Some(base)
      case _                          => None

  object TypeField:
    def unapply(expr: SymExpr): Option[SymExpr] = expr match
      case StaticField(base, "Type") => Some(base)
      case _                         => None
