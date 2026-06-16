package esmeta.solver

import esmeta.ir.{Op, Name}
import esmeta.state.Str
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.BaseUtils.*
import esmeta.util.Appender.*
import esmeta.util.Appender.{*, given}

// symbolic expression
sealed trait SymExpr {

  inline def /\(that: SymExpr): SymExpr = SAnd(this, that)
  inline def \/(that: SymExpr): SymExpr = SOr(this, that)
  inline def -->(that: SymExpr): SymExpr = SImply(this, that)
  inline def unary_! : SymExpr = SNot(this)

  override def toString: String = this match
    case SArg(i)       => s"#$i"
    case SThis         => "#THIS"
    case SArgsList     => "#ARGS_LIST"
    case SNewTarget    => "#NEW_TARGET"
    case SGlobal(name) => s"@$name"
    case SValue(ty)    => s"$ty"
    case SField(base, SValue(ty)) =>
      ty.getSingle match
        case One(Str(key)) => s"$base.$key"
        case _             => s"$base[$ty]"
    case SField(base, key)           => s"$base[$key]"
    case SNot(base)                  => s"(! $base)"
    case SAnd(left, right)           => s"(&& $left $right)"
    case SOr(left, right)            => s"(|| $left $right)"
    case SImply(premise, conclusion) => s"(=> $premise $conclusion)"
    case SEq(left, right)            => s"(= $left $right)"
    case SEqual(left, right)         => s"(== $left $right)"
    case SLt(left, right)            => s"(< $left $right)"
    case SExists(base, key)          => s"(exists $base $key)"
    case STypeCheck(base, ty)        => s"(? $base: $ty)"
    case SOp(op, args)               => s"([$op] ${args.mkString(", ")})"
}
object SymExpr {
  val T: SymExpr = SValue(TrueT)
  val F: SymExpr = SValue(FalseT)
  val PosInf: SymExpr = SValue(PosInfinityT)
  val NegInf: SymExpr = SValue(NegInfinityT)
}

// symbols
sealed trait Symbol extends SymExpr
case class SArg(i: Int) extends Symbol
case object SThis extends Symbol
case object SArgsList extends Symbol
case object SNewTarget extends Symbol
case class SGlobal(name: String) extends Symbol

// values
case class SValue(ty: ValueTy) extends SymExpr

// field access
case class SField(base: SymExpr, key: SymExpr) extends SymExpr

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
case class SExists(base: SymExpr, key: SymExpr) extends SymLogic
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

def SMath(n: BigDecimal): SValue = SValue(MathT(n))
def SInfinity(pos: Boolean): SValue = SValue(InfinityT(pos))
def SNumber(double: Double): SValue = SValue(NumberT(double))
def SBigInt(bigInt: BigInt): SValue = SValue(BigIntT(bigInt))
def SStr(str: String): SValue = SValue(StrT(str))
def SBool(b: Boolean): SValue = SValue(BoolT(b))
val SUndef: SValue = SValue(UndefT)
val SNull: SValue = SValue(NullT)
def SEnum(name: String): SValue = SValue(EnumT(name))
def SCodeUnit(c: Char): SValue = SValue(CodeUnitT)

// helper methods
import SymExpr.*
given Conversion[BigDecimal, SValue] with
  def apply(n: BigDecimal): SValue = SValue(MathT(n))
extension (k: Int) def n: SValue = SValue(BigIntT(k))
extension (d: Double) def f: SValue = SValue(NumberT(d))
extension (str: String)
  def n: SValue = SValue(BigIntT(str))
  def s: SValue = SValue(StrT(str))

// stringify a symbolic environment
given symExprRule: Rule[SymExpr] = (app, sexpr) => app >> sexpr.toString
// using pair of string and index
given Ordering[Symbol] = Ordering.by {
  case SArg(i)       => ("#", i)
  case SThis         => ("#THIS", 0)
  case SArgsList     => ("#ARGS_LIST", 0)
  case SNewTarget    => ("#NEW_TARGET", 0)
  case SGlobal(name) => (s"@$name", 0)
}
