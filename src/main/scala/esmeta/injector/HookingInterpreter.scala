package esmeta.injector

import esmeta.cfg.*
import esmeta.error.*
import esmeta.es.*
import esmeta.interpreter.*
import esmeta.ir.*
import esmeta.state.*
import esmeta.util.BaseUtils.*
import java.util.concurrent.TimeoutException
import scala.collection.mutable.{Set => MSet}

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

  // property writes from untaken branch paths (statically collected)
  private val untakenPropWrites: MSet[(Addr, String)] = MSet()

  // property writes that actually executed during current ExpressionStatement
  private val executedPropWrites: MSet[(Addr, String)] = MSet()

  // validated (expression, property) pairs for absent-property assertions
  private val validatedAbsentProperties: MSet[(Ast, String)] = MSet()
  def absentPropertyAssertions: Vector[(Ast, String)] =
    validatedAbsentProperties.toVector

  // Exit tag computed from final state
  lazy val exitTag: ExitTag = getExitTag(result)

  private val exprStmtEvalPattern =
    """^ExpressionStatement\[\d+,\d+\]\.Evaluation$""".r

  // Hook expression evaluation to track non-deterministic Expressions
  override def eval(expr: Expr): Value = expr match
    case ERandom() =>
      // mark nondeterminism flag
      _isNonDeterministic = true
      super.eval(expr)
    case _ => super.eval(expr)

  // Hook call evaluation to track actually executed property writes
  override def eval(call: Call): Unit = call.callInst match
    case ICall(_, EClo(name, _), ERef(target: Local) :: EStr(prop) :: _)
        if propWritingAlgos.contains(name) =>
      for {
        case addr: Addr <- st.context.locals.get(target)
      } executedPropWrites += ((addr, prop))
      super.eval(call)
    case _ => super.eval(call)

  // Hook branch movement to record property write effects from untaken paths
  override def moveBranch(branch: Branch, cond: Boolean): Unit =
    val untaken = if (cond) branch.elseNode else branch.thenNode
    untakenPropWrites ++= extractEffects(untaken)
    super.moveBranch(branch, cond)

  // Walk a branch path for property writing call effects, resolving to addresses
  private def extractEffects(node: Option[Node]): Set[(Addr, String)] =
    val visited = MSet[Node]()
    def walk(node: Option[Node]): Set[(Addr, String)] = node match
      case Some(n) if visited.contains(n) => Set.empty
      case Some(n) =>
        visited += n
        n match
          case block: Block => walk(block.next)
          case call: Call =>
            call.callInst match
              case ICall(_, EClo(name, _), ERef(x: Local) :: EStr(prop) :: _)
                  if propWritingAlgos.contains(name) =>
                st.context.locals.get(x) match
                  case Some(addr: Addr) => walk(call.next) + ((addr, prop))
                  case _                => walk(call.next)
              case _ => walk(call.next)
          case branch: Branch => walk(branch.thenNode) ++ walk(branch.elseNode)
      case None => Set.empty
    walk(node)

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
        expr = astValue.asAst.children(0).get
      } {
        lastEvaluatedExpr = Some((expr, value))
        isLastExprNonDeterministic = _isNonDeterministic
        if (!_isNonDeterministic) for {
          resultAddr <- resolveResultToAddr(value)
          (targetAddr, propName) <- untakenPropWrites
          if targetAddr == resultAddr
          if !executedPropWrites.contains((resultAddr, propName))
        } validatedAbsentProperties += ((expr, propName))
      }
      untakenPropWrites.clear()
      executedPropWrites.clear()
      _isNonDeterministic = false
      super.eval(cursor)
    case _ => super.eval(cursor)

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

  // manually selected algorithms, whose purpose is writing property
  val propWritingAlgos: Set[String] = Set(
    "CreateDataProperty",
    "CreateDataPropertyOrThrow",
    "CreateNonEnumerableDataPropertyOrThrow",
    "DefineMethodProperty",
    "DefinePropertyOrThrow",
    "OrdinaryDefineOwnProperty",
    "Set",
  )
}
