package synth262.error

import synth262.LINE_SEP
import synth262.ir.Param

sealed abstract class AnalysisError(msg: String)
  extends Synth262Error(msg, s"AnalysisError")

// not supported
case class NotSupportedOperation(obj: Any, method: String)
  extends AnalysisError(s"${obj.getClass.getName}.$method is not supported")

// imprecise
case class AnalysisImprecise(msg: String) extends AnalysisError(msg)

// type checking failure
case class TyCheckFail(msg: Option[String])
  extends AnalysisError("type checking failed." + msg.fold("")(LINE_SEP + _))
