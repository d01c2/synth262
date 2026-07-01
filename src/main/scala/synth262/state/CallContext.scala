package synth262.state

import synth262.cfg.*
import synth262.ir.{Func => IRFunc, *}

/** IR calling contexts */
case class CallContext(context: Context, retId: Local) extends StateElem {

  /** function name * */
  def name: String = context.func.irFunc.name

  /** copy contexts */
  def copied: CallContext = copy(context = context.copied)
}
