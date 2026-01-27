package esmeta.injector.util

import esmeta.injector.*
import esmeta.util.*
import esmeta.util.Appender.*

/** stringifier for injector elements */
object Stringifier {
  val stringifier = new Stringifier()
  export stringifier.given
}

class Stringifier {
  val msg = "\"detailed description needed\""

  given conformTestRule: Rule[ConformTest] = (app, test) =>
    val ConformTest(_, script, exitTag, throwExpr) = test

    if (script.nonEmpty) app >> script

    exitTag match
      case ExitTag.ThrowValue(Some(name)) =>
        throwExpr.foreach { expr =>
          app.wrap(s"assert.throws($name, function () {", s"}, $msg);") {
            app :> expr >> ";"
          }
        }
      case _ => ()
    app
}
