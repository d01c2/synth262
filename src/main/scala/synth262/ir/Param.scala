package synth262.ir

import synth262.ir.util.Parser
import synth262.spec.{Param => SpecParam}

/** IR function parameters */
case class Param(
  lhs: Name,
  ty: Type = UnknownType,
  optional: Boolean = false,
  specParam: Option[SpecParam] = None,
) extends IRElem
object Param extends Parser.From(Parser.param)
