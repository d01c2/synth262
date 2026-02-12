package esmeta.injector

import esmeta.cfg.CFG
import esmeta.es.*
import esmeta.injector.util.*
import esmeta.state.*
import esmeta.util.BaseUtils.*

/** assertion injector */
class Injector(cfg: CFG, interp: HookingInterpreter, testContent: String) {
  import Assertion.*, ExpectedValue.*

  /** final state */
  private lazy val finalState: State = interp.result

  /** last evaluated Expression with its evaluated value */
  private lazy val lastEvaluatedExpr: Option[(Ast, Value)] =
    finalState
    interp.lastEvaluatedExpr

  /** source text of the expression that caused a throw (for wrapping) */
  lazy val throwTargetSource: Option[String] =
    if (isNormalExit) None
    else lastEvaluatedExpr.map(_._1.toString(grammar = Some(cfg.grammar)))

  /** generated conformance test */
  lazy val conformTest: ConformTest =
    ConformTest(scriptWithAssertions.trim, exitTag, throwTargetSource)

  /** original script */
  lazy val originalScript: String = finalState.cachedSourceText.get

  /** expression eligible for assertion (normal exit, deterministic) */
  private lazy val assertableExpr: Option[(Ast, Value)] =
    lastEvaluatedExpr.filter { _ =>
      isNormalExit && !interp.isLastExprNonDeterministic
    }

  /** script with value and property assertions appended */
  lazy val scriptWithAssertions: String =
    val stringifier = Stringifier()
    import stringifier.given

    /** Value assertion for the last deterministic expression */
    val valueAssertion = assertableExpr.flatMap { (expr, value) =>
      val src = expr.toString(grammar = Some(cfg.grammar))
      toExpectedValue(value).map {
        case Simple(sv)      => SameValue(src, sv)
        case Array(elements) => CompareArray(src, elements)
      }
    }

    /** Absent-property assertions from false property-check branches */
    val propAssertions = interp.absentPropertyAssertions.map { (expr, prop) =>
      VerifyProperty(expr.toString(grammar = Some(cfg.grammar)), prop)
    }

    val assertions =
      (valueAssertion.toVector ++ propAssertions).map(stringify(_))

    val baseScript: String =
      if (!isNormalExit)
        (for {
          (ast, _) <- lastEvaluatedExpr
          loc <- ast.loc
        } yield testContent.take(loc.start.offset).trim)
          .getOrElse(testContent.trim)
      else if (assertions.nonEmpty)
        assertableExpr
          .flatMap((expr, _) => expr.loc)
          .fold(testContent.trim) { loc =>
            removeRange(testContent, loc.start.offset, loc.end.offset).trim
          }
      else testContent.trim

    (Vector(baseScript).filter(_.nonEmpty) ++ assertions).mkString("\n")

  /** exit status tag */
  lazy val exitTag: ExitTag = interp.exitTag

  /** whether the script terminated normally */
  lazy val isNormalExit: Boolean = exitTag == ExitTag.Normal

  // ---------------------------------------------------------------------------
  // private helpers
  // ---------------------------------------------------------------------------

  /** Remove text in [start, end) from source, skipping a trailing semicolon */
  private def removeRange(source: String, start: Int, end: Int): String =
    var i = end
    while (i < source.length && source(i).isWhitespace) i += 1
    if (i < source.length && source(i) == ';') i += 1
    source.take(start) + source.drop(i)

  /** convert a runtime Value to an assertable ExpectedValue, if possible */
  private def toExpectedValue(value: Value): Option[ExpectedValue] =
    value match
      case sv: SimpleValue => Some(Simple(sv))
      case addr: Addr =>
        finalState.unwrapComp(value) match
          case Some(unwrapped) => toExpectedValue(unwrapped)
          case None =>
            finalState(addr) match
              case obj: RecordObj => toExpectedArray(obj)
              case _              => None
      case _ => None

  /** extract array elements from a RecordObj (None if not array-like) */
  private def toExpectedArray(obj: RecordObj): Option[Array] =
    for {
      mapObj <- finalState.getMapObj(obj)
      case Number(length) <- finalState.getMapProp(mapObj, "length")
      len = length.toInt
    } yield {
      val elements = (0 until len).toVector.flatMap { i =>
        for {
          propValue <- finalState.getMapProp(mapObj, i.toString)
          extracted <- toExpectedValue(propValue)
        } yield extracted
      }
      Array(elements)
    }
}

object Injector {

  /** create a conformance test from source code */
  def apply(cfg: CFG, src: String): ConformTest =
    val interp = HookingInterpreter(cfg.init.from(src))
    new Injector(cfg, interp, src).conformTest
}
