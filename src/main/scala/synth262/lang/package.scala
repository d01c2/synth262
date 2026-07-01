package synth262.lang

import synth262.lang.util.*
import synth262.util.BaseUtils.*

/** Lang elements */
trait LangElem {

  override def toString: String = toString(true, false)

  /** stringify with options */
  def toString(detail: Boolean = true, location: Boolean = false): String = {
    val stringifier = LangElem.getStringifier(detail, location)
    import stringifier.elemRule
    stringify(this)
  }
}
object LangElem {
  val getStringifier =
    cached[(Boolean, Boolean), Stringifier] { Stringifier(_, _) }
}
