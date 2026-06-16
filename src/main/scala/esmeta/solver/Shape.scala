package esmeta.solver

import esmeta.state.*
import esmeta.ty.*
import esmeta.util.Appender.*
import esmeta.util.Appender.{*, given}

// shape of a symbolic value
case class Shape(
  ty: ValueTy,
) {
  // bottom check
  def isBottom: Boolean = ty.isBottom

  // partial order between shapes
  def <=(that: Shape): Boolean = this.ty <= that.ty

  // union of two shapes
  def ||(that: Shape): Shape = copy(this.ty || that.ty)

  // intersection of two shapes
  def &&(that: Shape): Shape = copy(this.ty && that.ty)

  // pruning of a shape by another shape
  def --(that: Shape): Shape = copy(this.ty -- that.ty)

  // get a JavaScript expression representing the shape
  def getJSExpr: Option[String] = getJSExpr(ty)

  def getJSExpr(ty: ValueTy): Option[String] =
    if (ty.number.contains(Number(0))) Some("0")
    else if (!ty.undef.isBottom) Some("undefined")
    else if (!ty.nullv.isBottom) Some("null")
    else if (ty.str.contains(Str(""))) Some("\"\"")
    else if (ty.bool.contains(false)) Some("false")
    else if (ty.bool.contains(true)) Some("true")
    else None
}
object Shape {
  val Top: Shape = Shape(AnyT)
  val Bottom: Shape = Shape(BotT)
  val Undef: Shape = Shape(UndefT)
  def apply(ty: Ty): Shape = Shape(ty.toValue)
}

// stringify a shape
given rule: Rule[Shape] = (app, shape) => {
  app >> shape.ty.toString
}
