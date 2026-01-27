package esmeta.injector

import esmeta.error.*
import esmeta.es.*
import esmeta.interpreter.*
import esmeta.ir.*
import esmeta.state.*
import esmeta.util.BaseUtils.*
import java.util.concurrent.TimeoutException
import scala.collection.mutable.{ListBuffer, Set => MSet}
import scala.util.matching.Regex

/** Hooking interpreter to capture ExpressionStatement evaluations */
class HookingInterpreter(val initSt: State) extends Interpreter(initSt) {

  /** captured (Expression, Value) pairs from ExpressionStatement evaluations */
  val capturedExprs: ListBuffer[(Ast, Value)] = ListBuffer()

  /** Expression ASTs whose evaluation involved non-deterministic operations */
  // TODO: Only tracks ERandom for now; need to consider other non-deterministic operations
  val nondetExprs: MSet[Ast] = MSet()

  /** Exit tag computed from final state */
  lazy val exitTag: ExitTag = computeExitTag(result)

  private val ExprStmtEvalFuncName: Regex =
    """^ExpressionStatement\[\d+,\d+\]\.Evaluation$""".r

  /** Check if AST is from harness */
  private def isFromHarness(ast: Ast): Boolean = (for {
    loc <- ast.loc
    filename <- loc.filename
  } yield filename.contains("test262/harness")).getOrElse(false)

  /** Extract Expression from ExpressionStatement AST */
  private def extractExpr(exprStmt: Ast): Ast = exprStmt.children(0).get

  /** Find enclosing ExpressionStatement from call stack */
  private def enclosingExprStmt: Option[Ast] =
    (st.context :: st.callStack.map(_.context)).collectFirst {
      case ctxt if ExprStmtEvalFuncName.matches(ctxt.func.name) =>
        ctxt.locals.get(NAME_THIS).map(astValue => extractExpr(astValue.asAst))
    }.flatten

  /** Hook expression evaluation to track non-deterministic Expressions */
  override def eval(expr: Expr): Value = expr match
    case ERandom() =>
      enclosingExprStmt.foreach(nondetExprs += _)
      super.eval(expr)
    case _ => super.eval(expr)

  /** transition for cursors - hooks ExpressionStatement exit */
  override def eval(cursor: Cursor): Boolean = cursor match
    case ExitCursor(func) if ExprStmtEvalFuncName.matches(func.name) =>
      for {
        (_, value) <- st.context.retVal
        astValue <- st.context.locals.get(NAME_THIS)
        exprStmt = astValue.asAst
        if !isFromHarness(exprStmt)
        expr = extractExpr(exprStmt)
      } capturedExprs += ((expr, value))
      try super.eval(cursor)
      catch { case e: InterpreterError => throw InterpreterErrorAt(e, cursor) }
    case _ =>
      try super.eval(cursor)
      catch { case e: InterpreterError => throw InterpreterErrorAt(e, cursor) }

  /** Compute exit tag from final state */
  private def computeExitTag(st: State): ExitTag =
    try {
      def getErrorName(error: Value): Option[String] = for {
        case proto: Addr <- Some(st(error, Str("Prototype")))
        case ctor: Addr <- st.getProp(proto, "constructor")
        case Str(name) <- st.getProp(ctor, "name")
      } yield name

      st(GLOBAL_RESULT) match
        case Undef => ExitTag.Normal
        case addr: Addr =>
          st(addr) match
            case ListObj(values) =>
              ExitTag.ThrowValue(values.headOption.flatMap(getErrorName))
            case _ => raise(s"unexpected exit status: ${st.getString(addr)}")
        case v => raise(s"unexpected exit status: ${st.getString(v)}")
    } catch {
      case _: TimeoutException   => ExitTag.Timeout
      case e: InterpreterErrorAt => ExitTag.SpecError(e.error, e.cursor)
    }
}
