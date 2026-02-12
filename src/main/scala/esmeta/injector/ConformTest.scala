package esmeta.injector

import esmeta.injector.util.*
import esmeta.util.BaseUtils.*

/** conformance test */
case class ConformTest(
  script: String,
  exitTag: ExitTag,
  throwTargetSource: Option[String],
) {
  override def toString: String =
    val stringifier = Stringifier()
    import stringifier.given
    stringify(this)
}
