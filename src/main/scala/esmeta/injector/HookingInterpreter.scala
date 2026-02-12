package esmeta.injector

import esmeta.cfg.*
import esmeta.error.*
import esmeta.es.*
import esmeta.interpreter.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.state.*
import esmeta.util.BaseUtils.*
import java.util.concurrent.TimeoutException
import scala.collection.mutable.{ListBuffer, Set => MSet}
import scala.util.matching.Regex

/** Hooking interpreter for assertion generation */
class HookingInterpreter(val initSt: State) extends Interpreter(initSt) {
  import HookingInterpreter.*

  // last ExpressionStatement result captured during evaluation
  var lastEvaluatedExpr: Option[(Ast, Value)] = None

  // whether the last evaluated expression involved non-deterministic operations
  // FIXME: Only tracks ERandom for now; need to consider other non-deterministic operations
  var isLastExprNonDeterministic: Boolean = false

  // whether the current ExpressionStatement evaluation is non-deterministic
  private var _isNonDeterministic: Boolean = false

  // locals assigned by property-reading algorithm calls, scoped by function
  private val propertyCheckLocals: MSet[(Func, Local)] = MSet()

  // pending effects from untaken branches, awaiting validation at ExprStmt exit
  private val pendingEffects: ListBuffer[(Addr, String)] = ListBuffer()

  // validated (expression, property) pairs for absent-property assertions
  private val validatedAbsentProperties: MSet[(Ast, String)] = MSet()
  def absentPropertyAssertions: Vector[(Ast, String)] =
    validatedAbsentProperties.toVector

  // Exit tag computed from final state
  lazy val exitTag: ExitTag = getExitTag(result)

  private val exprStmtEvalPattern: Regex =
    """^ExpressionStatement\[\d+,\d+\]\.Evaluation$""".r

  private def getExpression(exprStmt: Ast): Ast = exprStmt.children(0).get

  // Hook expression evaluation to track non-deterministic Expressions
  override def eval(expr: Expr): Value = expr match
    case ERandom() => _isNonDeterministic = true; super.eval(expr)
    case _         => super.eval(expr)

  // Hook call evaluation to track property-checking calls
  override def eval(call: Call): Unit = call.callInst match
    case ICall(lhs, EClo(name, _), _) if propReadingAlgos.contains(name) =>
      propertyCheckLocals += ((st.func, lhs))
      super.eval(call)
    case _ => super.eval(call)

  // Hook branch movement to record pending effects from untaken branches
  override def moveBranch(branch: Branch, cond: Boolean): Unit =
    if (!cond && isPropertyCheckBranch(branch)) for {
      (targetExpr, writtenProp) <- extractEffects(branch.thenNode)
      targetAddr <- resolveExprToAddr(targetExpr)
    } pendingEffects += ((targetAddr, writtenProp))
    super.moveBranch(branch, cond)

  // Check if a branch condition depends on a property-check result
  private def isPropertyCheckBranch(branch: Branch): Boolean =
    branch.cond match
      case ERef(x: Local) => isTracedToPropertyCheck(st.func, x)
      case _ =>
        extractLocalVar(branch.cond).exists(
          propertyCheckLocals.contains(st.func, _),
        )

  // Trace a variable back through assignments to a property-check origin
  private def isTracedToPropertyCheck(func: Func, x: Local): Boolean =
    propertyCheckLocals.contains((func, x)) || (for {
      case block: Block <- func.nodes
      inst <- block.insts
      y <- inst match
        case ILet(lhs, expr) if lhs == x           => extractLocalVar(expr)
        case IAssign(lhs: Local, expr) if lhs == x => extractLocalVar(expr)
        case _                                     => None
      if propertyCheckLocals.contains((func, y))
    } yield ()).nonEmpty

  // Walk the untaken true branch for property-writing call effects
  private def extractEffects(node: Option[Node]): List[(Expr, String)] =
    val results = ListBuffer[(Expr, String)]()
    var current = node
    var depth = 0
    while (current.isDefined && depth < 20) {
      current.get match
        case block: Block => current = block.next
        case call: Call =>
          call.callInst match
            case ICall(_, EClo(name, _), target :: EStr(prop) :: _)
                if propWritingAlgos.contains(name) =>
              results += ((target, prop))
              current = call.next
            case _ => current = call.next
        case branch: Branch if branch.isAbruptNode => current = branch.elseNode
        case _: Branch                             => current = None
      depth += 1
    }
    results.toList

  // Resolve a local-variable expression to its runtime address
  private def resolveExprToAddr(expr: Expr): Option[Addr] = expr match
    case ERef(x: Local) =>
      st.context.locals.get(x).collect { case addr: Addr => addr }
    case _ => None

  // Resolve a result value to an address, unwrapping CompletionRecord
  private def resolveResultToAddr(value: Value): Option[Addr] = value match
    case addr: Addr =>
      st.unwrapComp(addr) match
        case Some(inner: Addr) => Some(inner)
        case _                 => Some(addr)
    case _ => None

  // Hook cursor transition to capture ExpressionStatement exit
  override def eval(cursor: Cursor): Boolean = cursor match
    case ExitCursor(func) if exprStmtEvalPattern.matches(func.name) =>
      for {
        (_, value) <- st.context.retVal
        astValue <- st.context.locals.get(NAME_THIS)
        expr = getExpression(astValue.asAst)
      } {
        lastEvaluatedExpr = Some((expr, value))
        isLastExprNonDeterministic = _isNonDeterministic
        if (!_isNonDeterministic) for {
          resultAddr <- resolveResultToAddr(value)
          (targetAddr, propName) <- pendingEffects
          if targetAddr == resultAddr
        } validatedAbsentProperties += ((expr, propName))
      }
      pendingEffects.clear()
      _isNonDeterministic = false // reset
      try super.eval(cursor)
      catch { case e: InterpreterError => throw e }
    case _ =>
      try super.eval(cursor)
      catch { case e: InterpreterError => throw e }

  // get ExitTag from final state
  private def getExitTag(st: State): ExitTag =
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
      case _: TimeoutException => ExitTag.Timeout
      case e: InterpreterError => ExitTag.SpecError(e)
    }
}

object HookingInterpreter {

  // manually selected algorithms, whose purpose is reading property
  val propReadingAlgos: Set[String] = Set(
    "Get",
    "GetMethod",
    "HasOwnProperty",
    "HasProperty",
    "OrdinaryGetOwnProperty",
  )

  // manually selected algorithms, whose purpose is writing property
  val propWritingAlgos: Set[String] = Set(
    "CreateDataProperty",
    "CreateDataPropertyOrThrow",
    "CreateNonEnumerableDataPropertyOrThrow",
    "DefineMethodProperty",
    "DefinePropertyOrThrow",
    "Set",
  )

  // extract a Local variable reference from an expression
  def extractLocalVar(expr: Expr): Option[Local] = expr match
    case EBinary(BOp.Eq, ERef(x: Local), EBool(_)) => Some(x)
    case EBinary(BOp.Eq, EBool(_), ERef(x: Local)) => Some(x)
    case ERef(x: Local)                            => Some(x)
    case _                                         => None
}
