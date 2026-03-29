package esmeta.fuzzer.synthesizer

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Map => MMap}

class SpecStringSynthesizer(val base: Synthesizer)(using cfg: CFG)
  extends Synthesizer {
  import Coverage.*, SpecStringSynthesizer.*

  def name: String = "SpecStringSynthesizer"

  var targetCond: Option[Cond] = None

  def apply(
    name: String,
    args: List[Boolean],
    rhsIdx: Option[Int] = None,
  ): Syntactic =
    try { generateOne(name, args) }
    catch { case _: Exception => base(name, args, rhsIdx) }

  def apply(name: String): Lexical = base(name)

  // ---------------------------------------------------------------------------
  // Blind synthesis
  // ---------------------------------------------------------------------------

  def generateOne(prodName: String, args: List[Boolean]): Syntactic =
    val candidates = List(
      generateObject(args) -> 2,
      generateGetter(args) -> 1,
      generateSetter(args) -> 1,
      generateProxy(args) -> 2,
    )
    val all = targetCond.flatMap(c => findCondStr(c.branch.cond)) match
      case Some(str) => (generateString(str, args) -> 1) :: candidates
      case None      => candidates
    val chosen = weightedChoose(all)
    cfg
      .esParser(prodName, args)
      .from(chosen.toString(grammar = Some(cfg.grammar)))
      .asInstanceOf[Syntactic]

  private def generateString(str: String, args: List[Boolean]): Syntactic = cfg
    .esParser("PrimaryExpression", args)
    .from(s"\\'$str\\'")
    .asInstanceOf[Syntactic]

  private def generateObject(args: List[Boolean]): Syntactic =
    val k = chooseProp
    val v = choose(defaultValues)
    val raw = s"{ $k : $v }"
    cfg.esParser("PrimaryExpression", args).from(raw).asInstanceOf[Syntactic]

  private def generateProxy(args: List[Boolean]): Syntactic =
    val trap = chooseTrap
    val targetStr =
      if (fnProxyTraps.contains(trap)) "function ( ) { }" else "{}"
    val handler = choose(proxyTrapHandlers)
    val raw = s"(new Proxy($targetStr, { $trap : $handler }))"
    cfg.esParser("PrimaryExpression", args).from(raw).asInstanceOf[Syntactic]

  private def generateAccessor(
    kind: String,
    params: String,
    args: List[Boolean],
  ): Syntactic =
    val prop = chooseProp
    val templates = List(
      s"{ $kind $prop $params {} }",
      s"{ $kind $prop $params { throw 0 ; } }",
    )
    cfg
      .esParser("PrimaryExpression", args)
      .from(choose(templates))
      .asInstanceOf[Syntactic]

  private def generateGetter(args: List[Boolean]): Syntactic =
    generateAccessor("get", "()", args)

  private def generateSetter(args: List[Boolean]): Syntactic =
    generateAccessor("set", "(_)", args)

  // ---------------------------------------------------------------------------
  // Spec analysis
  // ---------------------------------------------------------------------------

  def chooseProp: String = chooseFrom(specProps, reachableProps, allProps)
  def chooseTrap: String = chooseFrom(specTraps, reachableTraps, allTrapsSet)

  private def chooseFrom(
    spec: Map[Func, Set[String]],
    reachable: Map[Func, Set[String]],
    all: Set[String],
  ): String =
    val cands = targetCond.flatMap(c => cfg.funcOf.get(c.branch)) match
      case Some(func) =>
        val s =
          if (randBool) reachable.getOrElse(func, Set())
          else spec.getOrElse(func, Set())
        if (s.isEmpty) all else s
      case None => all
    choose(cands)

  lazy val specProps: Map[Func, Set[String]] = {
    val acc = MMap[Func, Set[String]]().withDefaultValue(Set())
    class PropFinder(func: Func) extends esmeta.ir.util.UnitWalker {
      def addIfProp(e: Expr): Unit = e match
        case EStr(str) => acc.update(func, acc(func) + str)
        case ERef(Field(Global("SYMBOL"), EStr(sym))) =>
          acc.update(func, acc(func) + s"[ Symbol . $sym ]")
        case _ => ()
      override def walk(inst: Inst) = inst match
        case ICall(_, EClo(name, _), as) if propReadingAlgos.contains(name) =>
          as.foreach(addIfProp)
        case _ => super.walk(inst)
    }
    for (cfgFunc <- cfg.funcs)
      PropFinder(cfgFunc).walk(cfgFunc.irFunc.body)
    acc.toMap
  }

  lazy val allProps: Set[String] = specProps.values.flatten.toSet

  lazy val specTraps: Map[Func, Set[String]] = {
    val acc = MMap[Func, Set[String]]().withDefaultValue(Set())
    class TrapFinder(func: Func) extends esmeta.ir.util.UnitWalker {
      override def walk(inst: Inst) = inst match
        case ICall(_, EClo(name, _), _) if trapAlgos.contains(name) =>
          val trap = trapAlgos(name)
          acc.update(func, acc(func) + trap)
        case _ => super.walk(inst)
    }
    for (cfgFunc <- cfg.funcs)
      TrapFinder(cfgFunc).walk(cfgFunc.irFunc.body)
    acc.toMap
  }

  lazy val allTrapsSet: Set[String] = (objectProxyTraps ++ fnProxyTraps).toSet

  private def getReachableFuncs(root: Func): Set[Func] =
    def loop(func: Func, visited: Set[Func]): Set[Func] =
      if (visited.contains(func)) visited
      else {
        val callees = for {
          case Call(_, ICall(_, EClo(name, _), _), _) <- func.nodes
          if cfg.fnameMap.contains(name)
        } yield cfg.getFunc(name)
        callees.foldLeft(visited + func) { (acc, callee) => loop(callee, acc) }
      }
    loop(root, Set())

  private def reachableMap(
    spec: Map[Func, Set[String]],
  ): Map[Func, Set[String]] = (for {
    (func, _) <- spec
    reachable = getReachableFuncs(func)
    vals = reachable.flatMap(spec.getOrElse(_, Set()))
  } yield func -> vals).toMap

  lazy val reachableProps: Map[Func, Set[String]] = reachableMap(specProps)
  lazy val reachableTraps: Map[Func, Set[String]] = reachableMap(specTraps)
}

object SpecStringSynthesizer {
  import Coverage.*

  // ---------------------------------------------------------------------------
  // Spec constants
  // ---------------------------------------------------------------------------

  val propReadingAlgos = Set("Get", "GetMethod", "HasProperty")

  val trapAlgos: Map[String, String] = Map(
    "Get" -> "get",
    "GetV" -> "get",
    "GetMethod" -> "get",
    "Set" -> "set",
    "HasProperty" -> "has",
    "HasOwnProperty" -> "getOwnPropertyDescriptor",
    "DefinePropertyOrThrow" -> "defineProperty",
    "CreateDataProperty" -> "defineProperty",
    "CreateDataPropertyOrThrow" -> "defineProperty",
    "DeletePropertyOrThrow" -> "deleteProperty",
    "EnumerableOwnProperties" -> "ownKeys",
    "CopyDataProperties" -> "ownKeys",
    "GetOwnPropertyKeys" -> "ownKeys",
    "OrdinaryGetPrototypeOf" -> "getPrototypeOf",
    "OrdinarySetPrototypeOf" -> "setPrototypeOf",
    "IsExtensible" -> "isExtensible",
    "OrdinaryPreventExtensions" -> "preventExtensions",
    "TestIntegrityLevel" -> "isExtensible",
    "SetIntegrityLevel" -> "preventExtensions",
    "Call" -> "apply",
    "Construct" -> "construct",
  )

  // ---------------------------------------------------------------------------
  // Proxy
  // ---------------------------------------------------------------------------

  val objectProxyTraps: List[String] = List(
    "has",
    "get",
    "set",
    "defineProperty",
    "deleteProperty",
    "getOwnPropertyDescriptor",
    "ownKeys",
    "getPrototypeOf",
    "setPrototypeOf",
    "isExtensible",
    "preventExtensions",
  )

  val fnProxyTraps: List[String] = List("apply", "construct")

  val proxyTrapHandlers: List[String] = List(
    "function ( ) { return true ; }",
    "function ( ) { return 1 ; }",
    "function ( ) { return { } ; }",
    "function ( ) { return [ ] ; }",
    "function ( ) { return false ; }",
    "function ( ) { return null ; }",
    "function ( ) { return 0 ; }",
    "function ( ) { }",
    "function ( ) { throw 0 ; }",
  )

  // ---------------------------------------------------------------------------
  // Value atoms (disjoint)
  // ---------------------------------------------------------------------------

  private val falsyPrimitives = List("null", "undefined", "false", "0", "''")
  private val truthyPrimitives = List("true", "1", "Symbol ( )", "'str'")
  private val plainObjects = List("{}", "[]")
  private val callableForms = List(
    "function ( x ) { }",
    "function * ( x ) { }",
    "async function ( x ) { }",
    "async function * ( x ) { }",
    "( ) => { }",
    "function ( ) { throw 0 ; }",
  )
  private val iterators = List(
    "{ next ( ) { return { done : true , value : 0 } ; } }",
    "{ next ( ) { throw 0 ; } }",
  )
  private val thenables = List(
    "{ then ( r ) { r ( 0 ) ; } }",
    "{ then ( ) { throw 0 ; } }",
  )

  val defaultValues =
    falsyPrimitives ++ truthyPrimitives ++ plainObjects ++
    callableForms ++ iterators ++ thenables

  def findCondStr(e: Expr): Option[String] = e match
    case EBinary(BOp.Eq, EStr(str), _) => Some(str)
    case EBinary(BOp.Eq, _, EStr(str)) => Some(str)
    case _                             => None
}
