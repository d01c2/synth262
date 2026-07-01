package synth262.state

import synth262.cfg.*
import synth262.es.*
import synth262.spec.*
import synth262.util.UId

/** ECMAScript features */
sealed trait Feature extends StateElem with UId {
  def func: Func
  def head: Head
  def id: Int = func.id
}
case class SyntacticFeature(
  func: Func,
  head: SyntaxDirectedOperationHead,
) extends Feature
case class BuiltinFeature(
  func: Func,
  head: BuiltinHead,
) extends Feature
