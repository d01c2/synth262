package esmeta.injector.util

import esmeta.injector.*
import esmeta.state.*
import esmeta.util.Appender.*
import esmeta.util.BaseUtils.*

/** stringifier for injector elements */
object Stringifier {
  val stringifier = new Stringifier()
  export stringifier.given
}

class Stringifier {
  import Assertion.*, ExpectedValue.*

  val msg = "\"detailed description needed\""

  given conformTestRule: Rule[ConformTest] = (app, test) =>
    val ConformTest(_, script, exitTag, throwExpr) = test

    if (script.nonEmpty) app >> script

    exitTag match
      case ExitTag.Throw(Some(name)) =>
        throwExpr.foreach { expr =>
          app.wrap(
            s"assert.throws($name, function () {",
            s"}, $msg);",
          ) { app :> expr >> ";" }
        }
      case _ => ()
    app

  given assertionRule: Rule[Assertion] = (app, assertion) =>
    assertion match
      case SameValue(expr, expected) =>
        app >> s"assert.sameValue($expr, ${expectedValueStr(Simple(expected))}, $msg);"
      case CompareArray(expr, elements) =>
        app >> s"assert.compareArray($expr, ${expectedValueStr(Array(elements))}, $msg);"
      case VerifyProperty(expr, property) =>
        app >> s"verifyProperty($expr, \"$property\", undefined);"

  private def expectedValueStr(ev: ExpectedValue): String = ev match
    case Simple(sv)   => simpleValueStr(sv)
    case Array(elems) => arrayValueStr(elems)

  private def simpleValueStr(sv: SimpleValue): String = sv match
    case Number(Double.PositiveInfinity) => "Infinity"
    case Number(Double.NegativeInfinity) => "-Infinity"
    case Number(n) if n.isNaN            => "NaN"
    case Number(n)                       => s"$n"
    case BigInt(n)                       => s"${n}n"
    case Str(s)                          => s"\"$s\""
    case Bool(b)                         => s"$b"
    case Undef                           => "undefined"
    case Null                            => "null"

  private def arrayValueStr(elems: Vector[ExpectedValue]): String =
    elems.map(expectedValueStr).mkString("[", ", ", "]")

}
