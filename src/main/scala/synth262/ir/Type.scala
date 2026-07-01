package synth262.ir

import synth262.ir.util.Parser
import synth262.lang.{Type => LangType}
import synth262.ty.*

/** IR types */
case class Type(
  ty: Ty,
  langTy: Option[LangType] = None,
) extends IRElem {

  /** definite type check */
  inline def isDefined: Boolean = ty.isDefined

  /** imprecise type check */
  inline def isImprec: Boolean = ty.isImprec

  /** completion check */
  inline def isCompletion: Boolean = ty.isCompletion

  /** conversion to value type */
  inline def toValue: ValueTy = ty.toValue
}
object Type extends Parser.From(Parser.irType)

/** IR unknown types */
val UnknownType: Type = Type(UnknownTy())
def UnknownType(
  msg: String,
  langTy: Option[LangType] = None,
): Type = Type(UnknownTy(Some(msg)), langTy)
