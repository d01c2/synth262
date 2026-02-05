package esmeta.injector

import esmeta.{INJECT_LOG_DIR, TEST262_DIR}
import esmeta.cfg.CFG
import esmeta.es.*
import esmeta.state.*
import esmeta.util.SystemUtils.*
import java.io.PrintWriter

/** assertion injector */
case class Injector(
  cfg: CFG,
  interp: HookingInterpreter,
  harnessContent: String,
  testContent: String,
  log: Boolean,
) {
  import Assertion.*, ExpectedValue.*

  /** exit state */
  private lazy val exitSt: State = interp.result

  /** capture last ExpressionStatement evaluation and its value */
  private lazy val lastCapturedExpr: Option[(Ast, Value)] =
    exitSt
    interp.lastCapturedExpr

  /** the last Expression text (for throw wrapping) */
  lazy val throwingExprText: Option[String] =
    if (normalExit) None
    else lastCapturedExpr.map(_._1.toString(grammar = Some(cfg.grammar)))

  /** generated conformance test */
  lazy val conformTest: ConformTest =
    ConformTest(harnessContent, injectedScript.trim, exitTag, throwingExprText)

  /** injected script */
  lazy val result: ConformTest = conformTest

  /** original script (merged harness + test) */
  lazy val originalScript: String = exitSt.cachedSourceText.get

  /** Last expression to wrap (only for normal exit) */
  private lazy val exprToWrap: Option[(Ast, Value)] =
    if (normalExit)
      lastCapturedExpr.filterNot((expr, _) => interp.nondetExprs.contains(expr))
    else None

  /** Full script with assertion wrapping the last expression */
  lazy val injectedScript: String =
    val msg = "\"detailed description needed\""

    // For throw exit, truncate script at the throw point
    val truncateAt: Int =
      if (normalExit) testContent.length
      else
        (for {
          (ast, _) <- lastCapturedExpr
          loc <- ast.loc
        } yield loc.start.offset).getOrElse(testContent.length)

    // Extend end offset to include trailing semicolon
    def extendToSemicolon(end: Int): Int =
      var i = end
      while (i < testContent.length && testContent(i).isWhitespace) i += 1
      if (i < testContent.length && testContent(i) == ';') i + 1 else end

    // Build remaining script (with last expression removed if we're wrapping it)
    val remainingScript: String = exprToWrap match
      case Some((expr, _)) =>
        // Remove the last expression from the script
        (for {
          loc <- expr.loc
          (start, end) = (loc.start.offset, extendToSemicolon(loc.end.offset))
        } yield {
          val before = testContent.substring(0, start)
          val after =
            if (end < testContent.length) testContent.substring(end)
            else ""
          (before + after).trim
        }).getOrElse(testContent.trim)
      case None =>
        if (truncateAt >= testContent.length) testContent.trim
        else testContent.substring(0, truncateAt).trim

    // Generate assertion for the last expression (wrap directly, no temp var)
    val assertion: Option[Assertion] = exprToWrap.flatMap {
      case (expr, value) =>
        val exprText = expr.toString(grammar = Some(cfg.grammar))
        extractValue(value).map {
          case Simple(sv)      => SameValue(exprText, sv)
          case Array(elements) => CompareArray(exprText, elements)
        }
    }

    // Generate negative property assertions for property checking branches
    val negativeAssertions: Vector[Assertion] = interp.negativePropAssertions
      .filterNot((expr, _) => interp.nondetExprs.contains(expr))
      .map((expr, propName) =>
        val exprText = expr.toString(grammar = Some(cfg.grammar))
        VerifyProperty(exprText, propName),
      )

    import esmeta.injector.util.Stringifier.given
    import esmeta.util.BaseUtils.stringify
    val assertionStrs = assertion.map(a => stringify(a)).toVector
    val negativeAssertionStrs = negativeAssertions.map(a => stringify(a))

    // Combine: remaining script + assertion + negative assertions
    val parts =
      Vector(remainingScript).filter(_.nonEmpty) ++
      assertionStrs ++ negativeAssertionStrs
    parts.mkString("\n")

  /** exit status tag */
  lazy val exitTag: ExitTag = interp.exitTag

  /** normal termination */
  lazy val normalExit: Boolean = exitTag == ExitTag.Normal

  // ---------------------------------------------------------------------------
  // private helpers
  // ---------------------------------------------------------------------------
  // logging
  private lazy val pw: PrintWriter =
    println(s"[Injector] Logging into $INJECT_LOG_DIR...")
    mkdir(INJECT_LOG_DIR)
    getPrintWriter(s"$INJECT_LOG_DIR/log")
  private def log(data: Any): Unit = if (log) { pw.println(data); pw.flush() }

  // Only extracts assertable values (Primitive, Array) - skips reference types
  private def extractValue(value: Value): Option[ExpectedValue] =
    value match
      case sv: SimpleValue => Some(Simple(sv))
      case addr: Addr =>
        exitSt.unwrapComp(value) match
          case Some(unwrapped) => extractValue(unwrapped)
          case None =>
            exitSt(addr) match
              case obj: RecordObj => extractArray(obj) // None if not array
              case _              => None
      case _ => None

  // extract array elements from RecordObj (returns None if not an array)
  private def extractArray(obj: RecordObj): Option[ExpectedValue.Array] =
    for {
      mapObj <- exitSt.getMapObj(obj)
      case Number(lengthDouble) <- exitSt.getMapProp(mapObj, "length")
      length = lengthDouble.toInt
    } yield {
      val elements = (0 until length).toVector.flatMap { i =>
        for {
          propValue <- exitSt.getMapProp(mapObj, i.toString)
          extracted <- extractValue(propValue)
        } yield extracted
      }
      Array(elements)
    }
}

object Injector {
  import esmeta.es.util.{mergeStmt, flattenStmt}

  /** type aliases for code handling */
  private type CodeVec = (Vector[Ast], String)

  private def mergeCodeVec(a: CodeVec, b: CodeVec): CodeVec =
    (a._1 ++ b._1, a._2 + b._2)

  private def mergeCodeVecs(vs: CodeVec*): CodeVec =
    vs.foldLeft((Vector[Ast](), ""))((acc, cv) => mergeCodeVec(acc, cv))

  def apply(cfg: CFG, src: String, log: Boolean = false): ConformTest =
    val interp = HookingInterpreter(cfg.init.from(src))
    new Injector(cfg, interp, "", src, log).result

  /** injection from files with harness */
  def fromFile(cfg: CFG, filename: String, log: Boolean = false): ConformTest =
    val scriptParser = cfg.scriptParser
    // Parse harness files (sta.js + assert.js + propertyHelper.js) from test262/harness
    def getHarness(name: String): CodeVec =
      val (ast, str) = scriptParser.fromFileWithSourceText(
        s"$TEST262_DIR/harness/$name",
      )
      (flattenStmt(ast), str)
    val harness: CodeVec = mergeCodeVecs(
      getHarness("sta.js"), // default
      getHarness("assert.js"), // default
      getHarness("propertyHelper.js"), // for verifyProperty
    )
    val (harnessStmts, harnessStr) = harness
    // Parse test file with its filename preserved
    val (testAst, testStr) = scriptParser.fromFileWithSourceText(filename)
    val test: CodeVec = (flattenStmt(testAst), testStr)
    // Merge harness + test
    val (stmts, sourceText) = mergeCodeVec(harness, test)
    val ast = mergeStmt(stmts)
    // Run with merged AST
    val initSt = cfg.init.from(sourceText, Some(ast), filename = Some(filename))
    val interp = HookingInterpreter(initSt)
    new Injector(cfg, interp, harnessStr, testStr, log).result
}
