package esmeta.injector

import esmeta.error.*
import esmeta.state.*

/** exit status tag */
enum ExitTag:
  case Normal
  case Throw(errorName: Option[String])
  case Timeout
  case SpecError(error: ESMetaError)
