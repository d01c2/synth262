package synth262.analyzer.util

import synth262.analyzer.*
import synth262.analyzer.tychecker.*
import synth262.cfg.*
import synth262.ir.{IRElem, LangEdge}
import synth262.state.*
import synth262.ty.*
import synth262.ty.util.{Stringifier => TyStringifier}
import synth262.util.*
import synth262.util.Appender.*
import synth262.util.BaseUtils.*

trait StringifierDecl { self: Self =>

  /** stringifier for analyzer */
  class Stringifier(
    detail: Boolean,
    location: Boolean,
    asite: Boolean,
  ) {
    private val cfgStringifier = CFGElem.getStringifier(detail, location)
    import cfgStringifier.given

    private val irStringifier = IRElem.getStringifier(detail, location)
    import irStringifier.given

    /** elements */
    given elemRule: Rule[AnalyzerElem] = (app, elem) =>
      elem match
        case elem: ControlPoint => cpRule(app, elem)

    // control points
    given cpRule: Rule[ControlPoint] = (app, cp) =>
      app >> cp.func.name >> "[" >> cp.func.id >> "]:"
      app >> (cp match
        case NodePoint(_, node, view) => node.simpleString
        case ReturnPoint(func, view)  => "RETURN"
      )
      if (cp.view.isEmpty) app
      else app >> ":" >> cp.view

    given Rule[View] = viewRule(detail)
  }
}
