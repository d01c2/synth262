package esmeta.fuzzer

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.ty.*
import esmeta.util.BaseUtils.*
import io.circe.*, io.circe.syntax.*
import scala.collection.mutable.{Map => MMap, Set => MSet}
import scala.util.Try

/** Snippet storage for abrupt-completion-triggering code snippets */
class SnippetStorage(using val cfg: CFG) {
  import Code.*, Coverage.*, SnippetStorage.*

  private val analyzed: Map[String, Set[String]] = analyze()
  private val cached: MMap[String, MSet[String]] = MMap()

  /** get snippets for a function */
  def getSnippets(funcName: String): Set[String] =
    analyzed.getOrElse(funcName, Set()) ++
    cached.get(funcName).map(_.toSet).getOrElse(Set())

  /** get all snippets for each functions as JSON */
  def dumpContent: Json =
    val allFuncs = analyzed.keySet ++ cached.keySet
    JsonObject.fromIterable {
      allFuncs.toSeq.sorted.map { func =>
        val allSnippets =
          analyzed.getOrElse(func, Set()) ++
          cached.getOrElseUpdate(func, MSet()).toSet
        func -> allSnippets.toSeq.sorted.asJson
      }
    }.asJson

  /** cache snippets from successful mutation covering abrupt branches */
  def cache(
    orig: Code,
    mutant: Code,
    touchedCondViews: Map[CondView, Set[Target]],
  ): Unit = for {
    (cv, targets) <- touchedCondViews
    Cond(branch, cond) = cv.cond
    if branch.isAbruptNode && cond
    funcName <- findSourceFunc(cfg.funcOf(branch), branch)
    snippet <- diffSnippet(orig, mutant, targets) if snippet.nonEmpty
  } cached.getOrElseUpdate(funcName, MSet()) += snippet

  /** find the source function for an abrupt branch */
  def findSourceFunc(func: Func, branch: Branch): Option[String] =
    branch.cond match
      case ETypeCheck(ERef(local: Local), _) =>
        findCallForVar(func, branch, local)
      case _ => None

  // ---------------------------------------------------------------------------
  // private helpers for lightweight static analysis
  // ---------------------------------------------------------------------------
  private def analyze(): Map[String, Set[String]] =
    // find direct snippets from type checks leading to throws
    // e.g. If [...] is undefined, throw [...]
    val direct = MMap[String, Set[String]]()
    for {
      func <- cfg.funcs
      snippets = analyzeFunction(func)
      if snippets.nonEmpty
    } direct(func.name) = snippets

    // build call graph and propagate snippets to callers
    propagate(direct.toMap, buildCallGraph())

  private def analyzeFunction(func: Func): Set[String] =
    var result: Set[String] = Set()
    for {
      branch <- func.nodes.collect { case b: Branch => b }
      if !branch.isAbruptNode
      if branch.thenNode.exists(_.reachable.exists(isThrowNode))
    } branch.cond match
      case EBinary(BOp.Eq, ETypeOf(_), ERef(Global(name))) =>
        result ++= snippets(name)
      case ETypeCheck(_, ty) => result ++= snippets(ty)
      case _                 => ()
    result

  private def buildCallGraph(): Map[String, Set[String]] =
    val graph = MMap[String, Set[String]]()
    for {
      func <- cfg.funcs
      node <- func.nodes
      callee <- node match
        case c: Call => extractFuncName(c.callInst)
        case _       => None
    } graph(func.name) = graph.getOrElse(func.name, Set()) + callee
    graph.toMap

  private def propagate(
    direct: Map[String, Set[String]],
    callGraph: Map[String, Set[String]],
  ): Map[String, Set[String]] =
    // reverse call graph: callee -> callers
    val reverse = MMap[String, Set[String]]()
    for { (caller, callees) <- callGraph; callee <- callees }
      reverse(callee) = reverse.getOrElse(callee, Set()) + caller

    // fixed-point propagation
    val result = MMap[String, Set[String]]() ++= direct
    var changed = true
    while (changed) {
      changed = false
      for {
        (callee, snippets) <- result.toList
        caller <- reverse.getOrElse(callee, Set())
        current = result.getOrElse(caller, Set())
        merged = current ++ snippets
        if merged.size > current.size
      } { result(caller) = merged; changed = true }
    }
    result.toMap

  // ---------------------------------------------------------------------------
  // private helpers for runtime caching
  // ---------------------------------------------------------------------------
  private def diffSnippet(
    orig: Code,
    mutant: Code,
    targets: Set[Target],
  ): Option[String] = (orig, mutant) match
    case (orig: Normal, mut: Normal) if orig != mut =>
      targets.collectFirst {
        case t: Target.Normal => Try(t.loc.getString(mut.sourceText)).toOption
      }.flatten
    case (orig: Builtin, mut: Builtin) =>
      if (orig.thisArg != mut.thisArg) mut.thisArg
      else {
        val pairs = orig.args.zip(mut.args)
        pairs.collectFirst {
          case (origArg, mutArg) if origArg != mutArg => Some(mutArg)
        }.flatten
      }
    case _ => None

  private def findCallForVar(
    func: Func,
    branch: Branch,
    target: Local,
  ): Option[String] =
    val dataDeps = cfg.depGraph.dataDeps(func)
    dataDeps
      .useToDefs(branch)
      .getOrElse(target, Set())
      .collectFirst { case c: Call => extractFuncName(c.callInst) }
      .flatten
}

object SnippetStorage {

  /** ValueTy to JavaScript snippets mapping */
  private val snippetsFor: Map[ValueTy, Set[String]] = Map(
    UndefT -> Set("undefined"),
    NullT -> Set("null"),
    SymbolT -> Set("Symbol()"),
    StrT -> Set("\"\"", "\"test\""),
    NumberT -> Set("0", "NaN", "Infinity"),
    BoolT -> Set("true", "false"),
    ObjectT -> Set("{}", "[]"),
    BigIntT -> Set("0n", "1n"),
  )

  /** get snippets for a type name */
  def snippets(typeName: String): Set[String] =
    snippetsFor.getOrElse(ValueTy.fromTypeOf(typeName), Set())

  /** get snippets for an IR type */
  def snippets(ty: Type): Set[String] =
    val v = ty.ty.toValue
    snippetsFor.collect { case (t, s) if !(v && t).isBottom => s }.flatten.toSet

  /** check if node throws */
  def isThrowNode(node: Node): Boolean = node match
    case block: Block =>
      block.insts.exists {
        case IReturn(ERecord("ThrowCompletion", _)) => true
        case _                                      => false
      }
    case call: Call =>
      call.callInst match
        case ICall(_, EClo("ThrowCompletion", _), _) => true
        case _                                       => false
    case branch: Branch => branch.isAbruptNode

  /** extract function name from call instruction */
  def extractFuncName(inst: CallInst): Option[String] = inst match
    case ICall(_, EClo(name, _), _) => Some(name)
    case ICall(_, ECont(name), _)   => Some(name)
    case ISdoCall(_, _, name, _)    => Some(name)
    case _                          => None
}
