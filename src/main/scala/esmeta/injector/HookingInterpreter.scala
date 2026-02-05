package esmeta.injector

import esmeta.cfg.*
import esmeta.error.*
import esmeta.es.*
import esmeta.interpreter.*
import esmeta.ir.*
import esmeta.state.*
import esmeta.util.BaseUtils.*
import java.util.concurrent.TimeoutException
import scala.collection.mutable.{ListBuffer, Map => MMap, Set => MSet}
import scala.util.matching.Regex

/** Hooking interpreter for assertion generation */
class HookingInterpreter(val initSt: State) extends Interpreter(initSt) {
  import HookingInterpreter.*

  /** capture last ExpressionStatement evaluation and capture its value */
  var lastCapturedExpr: Option[(Ast, Value)] = None

  /** Expression ASTs whose evaluation involved non-deterministic operations */
  // TODO: Only tracks ERandom for now; need to consider other non-deterministic operations
  val nondetExprs: MSet[Ast] = MSet()

  /** tracked property checking calls */
  private val propCheckCalls: MMap[Local, String] = MMap()

  /** negative property assertions */
  private val negativeProps: MSet[(Ast, String)] = MSet()
  def negativePropAssertions: Vector[(Ast, String)] = negativeProps.toVector

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

  /** hook call evaluation to track property checking calls */
  override def eval(call: Call): Unit = call.callInst match
    case ICall(lhs, EClo(name, _), args) if propCheckAlgos.contains(name) =>
      extractPropName(args).foreach(propCheckCalls += lhs -> _)
      super.eval(call)
    case _ => super.eval(call)

  /** hook branch movement to track false property checking branches */
  override def moveBranch(branch: Branch, cond: Boolean): Unit =
    if (!cond) for {
      propName <- findPropForBranch(branch)
      expr <- enclosingExprStmt
    } negativeProps += ((expr, propName))
    super.moveBranch(branch, cond)

  /** find property name if branch depends on a property checking call */
  private def findPropForBranch(branch: Branch): Option[String] =
    branch.cond match
      case ERef(x: Local) => findPropFromVar(x)
      case _ => extractLocal(branch.cond).flatMap(propCheckCalls.get)

  /** trace variable back to property checking call */
  private def findPropFromVar(x: Local): Option[String] =
    propCheckCalls.get(x) match
      case Some(prop) => Some(prop)
      case None =>
        (for {
          case block: Block <- st.func.nodes
          inst <- block.insts
          y <- inst match
            case ILet(lhs, expr) if lhs == x           => extractLocal(expr)
            case IAssign(lhs: Local, expr) if lhs == x => extractLocal(expr)
            case _                                     => None
          prop <- propCheckCalls.get(y)
        } yield prop).headOption

  /** transition for cursors - hooks ExpressionStatement exit */
  override def eval(cursor: Cursor): Boolean = cursor match
    case ExitCursor(func) if ExprStmtEvalFuncName.matches(func.name) =>
      for {
        (_, value) <- st.context.retVal
        astValue <- st.context.locals.get(NAME_THIS)
        exprStmt = astValue.asAst
        if !isFromHarness(exprStmt)
        expr = extractExpr(exprStmt)
      } lastCapturedExpr = Some((expr, value))
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
              ExitTag.Throw(values.headOption.flatMap(getErrorName))
            case _ => raise(s"unexpected exit status: ${st.getString(addr)}")
        case v => raise(s"unexpected exit status: ${st.getString(v)}")
    } catch {
      case _: TimeoutException   => ExitTag.Timeout
      case e: InterpreterErrorAt => ExitTag.SpecError(e.error, e.cursor)
    }
}

object HookingInterpreter {
  // property checking algorithms
  val propCheckAlgos: Set[String] = Set("HasProperty")

  // extract first string literal from arguments
  def extractPropName(args: List[Expr]): Option[String] =
    args.collectFirst { case EStr(s) => s }

  // extract Local from expression
  def extractLocal(expr: Expr): Option[Local] = expr match
    case EBinary(BOp.Eq, ERef(x: Local), EBool(_)) => Some(x)
    case EBinary(BOp.Eq, EBool(_), ERef(x: Local)) => Some(x)
    case ERef(x: Local)                            => Some(x)
    case _                                         => None
}
