package synth262.injector

import synth262.injector.util.*
import synth262.util.BaseUtils.*

/** Injector elements */
trait InjectorElem {
  override def toString: String = toString()

  /** stringify with options */
  def toString(detail: Boolean = false): String = {
    val stringifier = InjectorElem.getStringifier(detail)
    import stringifier.elemRule
    stringify(this)
  }
}
object InjectorElem {
  val getStringifier =
    cached[Boolean, Stringifier] { Stringifier(_) }
}
