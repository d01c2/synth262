package esmeta.injector.util

import esmeta.injector.*
import esmeta.state.*
import esmeta.util.Appender.*
import esmeta.util.BaseUtils.*

/** stringifier for injector elements */
class Stringifier {
  import Assertion.*, ExpectedValue.*

  val description = "\"detailed description needed\""

  given conformTestRule: Rule[ConformTest] = (app, test) =>
    val ConformTest(script, exitTag, throwTarget) = test

    if (script.nonEmpty) app >> script

    (exitTag, throwTarget) match
      case (ExitTag.Throw(Some(error)), Some(expr)) =>
        app.wrap(
          s"assert.throws($error, function () {",
          s"}, $description);",
        ) { app :> expr >> ";" }
      case _ =>
    app

  given assertionRule: Rule[Assertion] = (app, assertion) =>
    assertion match
      case SameValue(exprSource, expected) =>
        app >> s"assert.sameValue($exprSource, ${expectedValueStr(Simple(expected))}, $description);"
      case CompareArray(exprSource, elements) =>
        app >> s"assert.compareArray($exprSource, ${expectedValueStr(Array(elements))}, $description);"
      case VerifyProperty(objSource, property) =>
        app >> s"verifyProperty($objSource, \"$property\", undefined);"

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
