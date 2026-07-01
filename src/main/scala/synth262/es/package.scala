package synth262.es

import synth262.cfg.*
import synth262.es.util.*
import synth262.spec.Grammar
import synth262.state.*
import synth262.util.BaseUtils.*

/** ECMAScript elements */
trait ESElem {
  override def toString: String = toString()

  /** stringify with options */
  def toString(
    detail: Boolean = true,
    location: Boolean = false,
    grammar: Option[Grammar] = None,
  ): String = {
    val stringifier = ESElem.getStringifier(detail, location, grammar)
    import stringifier.elemRule
    stringify(this)
  }
}
object ESElem {
  val getStringifier =
    cached[(Boolean, Boolean, Option[Grammar]), Stringifier] {
      Stringifier(_, _, _)
    }
}

/** create a record object with concrete methods */
def recordObj(tname: String)(using CFG): RecordObj = recordObj(tname)()

/** create a record object with concrete methods */
def recordObj(tname: String)(
  fields: (String, Value)*,
)(using cfg: CFG): RecordObj = recordObj(tname)(fields)

/** create a record object with concrete methods */
def recordObj(tname: String)(
  fields: Iterable[(String, Value)],
)(using cfg: CFG): RecordObj = {
  val obj = RecordObj(tname, fields.toMap)
  for {
    (name, f) <- cfg.tyModel.methodOf(tname)
  } obj.map += name -> Clo(cfg.fnameMap(f), Map())
  obj
}
