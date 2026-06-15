package esmeta.solver

import esmeta.ir.{Op, Name}

// symbolic expression
sealed trait SymExpr {

  inline def /\(that: SymExpr): SymExpr = SAnd(this, that)
  inline def \/(that: SymExpr): SymExpr = SOr(this, that)
  inline def -->(that: SymExpr): SymExpr = SImply(this, that)
  inline def unary_! : SymExpr = SNot(this)

  override def toString: String = this match
    case SArg(i)                          => s"#$i"
    case SThis                            => "#THIS"
    case SArgsList                        => "#ARGS_LIST"
    case SNewTarget                       => "#NEW_TARGET"
    case SGlobal(name)                    => s"@$name"
    case SMath(n)                         => n.toString
    case SInfinity(pos)                   => if (pos) "+INF" else "-INF"
    case SNumber(Double.PositiveInfinity) => "+NUM_INF"
    case SNumber(Double.NegativeInfinity) => "-NUM_INF"
    case SNumber(d) if d.isNaN            => "NaN"
    case SNumber(d)                       => s"${d}f"
    case SBigInt(bigInt)                  => s"${bigInt}n"
    case SStr(str)                        => s""""$str""""
    case SBool(b)                         => b.toString
    case SUndef                           => "undefined"
    case SNull                            => "null"
    case SEnum(name)                      => s"~$name~"
    case SCodeUnit(c)                     => s"'$c'"
    case SField(base, SStr(key))          => s"$base.$key"
    case SField(base, key)                => s"$base[$key]"
    case SNot(base)                       => s"!($base)"
    case SAnd(left, right)                => s"($left /\\ $right)"
    case SOr(left, right)                 => s"($left \\/ $right)"
    case SImply(premise, conclusion)      => s"(($premise) => ($conclusion))"
    case SEq(left, right)                 => s"($left = $right)"
    case SEqual(left, right)              => s"($left = $right)"
    case SLt(left, right)                 => s"($left < $right)"
    case SHas(base, key)                  => s"($base has $key)"
    case STypeCheck(base, ty)             => s"(? $base: $ty)"
    case SOp(op, args)                    => s"([$op] ${args.mkString(", ")})"
    case SCall(name, args)                => s"$name(${args.mkString(", ")})"
}
object SymExpr {
  val T: SymExpr = SBool(true)
  val F: SymExpr = SBool(false)
  val PosInf: SymExpr = SInfinity(true)
  val NegInf: SymExpr = SInfinity(false)
}

// base cases
sealed trait SymBase extends SymExpr
case class SArg(i: Int) extends SymBase
case object SThis extends SymBase
case object SArgsList extends SymBase
case object SNewTarget extends SymBase
case class SGlobal(name: String) extends SymBase

// literal cases
sealed trait SymLit extends SymExpr
case class SMath(n: BigDecimal) extends SymLit
case class SInfinity(pos: Boolean) extends SymLit
case class SNumber(double: Double) extends SymLit
case class SBigInt(bigInt: BigInt) extends SymLit
case class SStr(str: String) extends SymLit
case class SBool(b: Boolean) extends SymLit
case object SUndef extends SymLit
case object SNull extends SymLit
case class SEnum(name: String) extends SymLit
case class SCodeUnit(c: Char) extends SymLit

// field access
case class SField(base: SymExpr, key: SymExpr) extends SymExpr

// function application
case class SCall(name: String, args: List[SymExpr]) extends SymExpr

// operation application
case class SOp(op: Op, args: List[SymExpr]) extends SymExpr

// logical operations
sealed trait SymLogic extends SymExpr
case class SNot(base: SymExpr) extends SymLogic
case class SAnd(left: SymExpr, right: SymExpr) extends SymLogic
case class SOr(left: SymExpr, right: SymExpr) extends SymLogic
case class SImply(premise: SymExpr, conclusion: SymExpr) extends SymLogic
case class SEq(left: SymExpr, right: SymExpr) extends SymLogic
case class SEqual(left: SymExpr, right: SymExpr) extends SymLogic
case class SLt(left: SymExpr, right: SymExpr) extends SymLogic
case class SHas(base: SymExpr, key: SymExpr) extends SymLogic
case class STypeCheck(base: SymExpr, ty: TypeCase) extends SymLogic

enum TypeCase:
  case Undefined
  case Null
  case Boolean
  case Number
  case String
  case BigInt
  case Symbol
  case Object

  override def toString: String = this match
    case Undefined => "Undefined"
    case Null      => "Null"
    case Boolean   => "Boolean"
    case Number    => "Number"
    case String    => "String"
    case BigInt    => "Bigint"
    case Symbol    => "Symbol"
    case Object    => "Object"

// helper methods
import SymExpr.*
given Conversion[BigDecimal, SMath] with
  def apply(n: BigDecimal): SMath = SMath(n)
extension (k: Int) def n: SBigInt = SBigInt(k)
extension (d: Double) def f: SNumber = SNumber(d)
extension (str: String)
  def n: SBigInt = SBigInt(BigInt(str))
  def s: SStr = SStr(str)
