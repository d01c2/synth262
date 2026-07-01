package synth262.state

import synth262.ir.Var

/** IR reference target */
sealed trait RefTarget extends StateElem
case class VarTarget(x: Var) extends RefTarget
case class FieldTarget(base: Value, field: Value) extends RefTarget
