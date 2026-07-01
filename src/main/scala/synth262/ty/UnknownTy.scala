package synth262.ty

import synth262.cfg.CFG
import synth262.error.NotSupported
import synth262.error.NotSupported.Category.Type
import synth262.state.*
import synth262.ty.util.*

/** unknown type */
case class UnknownTy(msg: Option[String] = None) extends Ty {

  /** completion check */
  def isCompletion: Boolean = msg.exists(_ contains "Completion")

  /** value containment check */
  def contains(value: Value, heap: Heap): Boolean =
    throw NotSupported(Type)(msg.toList)
}
object UnknownTy extends Parser.From(Parser.unknownTy):
  def apply(str: String): UnknownTy = UnknownTy(Some(str))
