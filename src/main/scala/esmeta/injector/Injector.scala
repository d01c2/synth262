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

  /** exit state */
  private lazy val exitSt: State = interp.result

  /** captured (Expression, expected value) pairs */
  private lazy val capturedExprs: Vector[(Ast, Value)] =
    exitSt
    interp.capturedExprs.toVector

  /** the last expression text (for throw wrapping) */
  lazy val throwingExprText: Option[String] =
    if (normalExit) None
    else
      capturedExprs.lastOption.map {
        case (expr, _) => expr.toString(grammar = Some(cfg.grammar))
      }

  /** generated conformance test */
  lazy val conformTest: ConformTest =
    ConformTest(harnessContent, injectedScript.trim, exitTag, throwingExprText)

  /** injected script */
  lazy val result: ConformTest = conformTest

  /** original script (merged harness + test) */
  lazy val originalScript: String = exitSt.cachedSourceText.get

  /** Expressions to capture with temp variables */
  private lazy val exprsToCapture: Vector[(Ast, Value)] =
    val candidates =
      if (normalExit) capturedExprs // all expressions
      else capturedExprs.dropRight(1) // all except the throwing one
    // Filter out non-deterministic expressions
    candidates.filterNot { case (expr, _) => interp.nondetExprs.contains(expr) }

  /** Full script with temp vars and assertions */
  lazy val injectedScript: String =
    val msg = "\"detailed description needed\""

    // For throw exit, truncate script at the throw point
    val truncateAt: Int =
      if (normalExit) testContent.length
      else
        (for {
          (ast, _) <- capturedExprs.lastOption
          loc <- ast.loc
        } yield loc.start.offset).getOrElse(testContent.length)

    // Extend end offset to include trailing semicolon
    def extendToSemicolon(end: Int): Int =
      var i = end
      while (i < testContent.length && testContent(i).isWhitespace) i += 1
      if (i < testContent.length && testContent(i) == ';') i + 1 else end

    // Build remaining script
    val remainingScript: String =
      if (exprsToCapture.isEmpty)
        if (truncateAt >= testContent.length) testContent
        else testContent.substring(0, truncateAt).trim
      else
        val removals = (for {
          (expr, _) <- exprsToCapture
          loc <- expr.loc
          (start, end) = (loc.start.offset, loc.end.offset)
        } yield (start, extendToSemicolon(end))).sortBy(_._1)
        val result = new StringBuilder
        var lastEnd = 0
        for (
          (start, end) <- removals
          if start >= lastEnd && start < truncateAt
        ) do
          if (start > lastEnd)
            result.append(
              testContent.substring(lastEnd, math.min(start, truncateAt)),
            )
          lastEnd = end
        if (lastEnd < truncateAt)
          result.append(testContent.substring(lastEnd, truncateAt))
        result.toString.trim

    // Generate temp var declarations and assertions
    val captured: Vector[(String, SimpleValue)] =
      exprsToCapture.flatMap {
        case (expr, value) =>
          val exprText = expr.toString(grammar = Some(cfg.grammar))
          extractSimpleValue(value).map(sv => (exprText, sv))
      }

    val tempVars = captured.zipWithIndex.map {
      case ((exprText, _), idx) =>
        s"var __temp${idx + 1} = $exprText;"
    }
    val assertions = captured.zipWithIndex.map {
      case ((_, value), idx) =>
        s"assert.sameValue(__temp${idx + 1}, ${valueToString(value)}, $msg);"
    }

    // Combine: remaining script + temp vars + assertions
    val parts =
      Vector(remainingScript).filter(_.nonEmpty) ++ tempVars ++ assertions
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

  // extract SimpleValue from a Value, unwrapping CompletionRecords
  private def extractSimpleValue(value: Value): Option[SimpleValue] =
    value match
      case sv: SimpleValue => Some(sv)
      case addr: Addr =>
        exitSt(addr) match
          case RecordObj("CompletionRecord", map) =>
            map.get("Type") match
              case Some(Enum("normal")) =>
                map.get("Value").flatMap(extractSimpleValue)
              case _ => None
          case _ => None // TODO: handle object values
      case _ => None

  // convert SimpleValue to string for assertion
  private def valueToString(value: SimpleValue): String = value match
    case Number(n) => n.toString
    case v         => v.toString
}

object Injector {
  import esmeta.es.util.{mergeStmt, flattenStmt}

  /** type aliases for code handling */
  private type CodeVec = (Vector[Ast], String)

  private def mergeCodeVec(a: CodeVec, b: CodeVec): CodeVec =
    (a._1 ++ b._1, a._2 + b._2)

  def apply(cfg: CFG, src: String, log: Boolean = false): ConformTest =
    val interp = HookingInterpreter(cfg.init.from(src))
    new Injector(cfg, interp, "", src, log).result

  /** injection from files with harness */
  def fromFile(cfg: CFG, filename: String, log: Boolean = false): ConformTest =
    val scriptParser = cfg.scriptParser
    // Parse harness files (sta.js + assert.js) from test262/harness
    def getHarness(name: String): CodeVec =
      val (ast, str) = scriptParser.fromFileWithSourceText(
        s"$TEST262_DIR/harness/$name",
      )
      (flattenStmt(ast), str)
    val harness: CodeVec =
      mergeCodeVec(getHarness("sta.js"), getHarness("assert.js"))
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
