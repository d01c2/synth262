package esmeta.fuzzer.synthesizer

import esmeta.cfg.{CFG, Func, Call, Branch}
import esmeta.es.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Map => MMap}

/** A spec string synthesizer that wraps a base synthesizer */
class SpecStringSynthesizer(val base: Synthesizer)(using cfg: CFG)
  extends Synthesizer {
  import SpecStringSynthesizer.*

  def name: String = "SpecStringSynthesizer"

  var targetBranch: Option[Branch] = None

  // derived from targetBranch
  private def targetFunc: Option[Func] = targetBranch.flatMap(cfg.funcOf.get)
  private def targetCondStr: Option[String] =
    targetBranch.flatMap(b => findCondStr(b.cond))

  /** for syntactic production: try spec string generation, fallback to base */
  def apply(
    name: String,
    args: List[Boolean],
    rhsIdx: Option[Int] = None,
  ): Syntactic =
    try { generateOne(name, args) }
    catch { case _: Exception => base(name, args, rhsIdx) }

  /** for lexical production: delegate to base */
  def apply(name: String): Lexical = base(name)

  /** generate one spec-guided AST node at the given production level */
  def generateOne(prodName: String, args: List[Boolean]): Syntactic =
    val candidates = List(
      generateObject(args) -> 1,
      generateAccessor(args) -> 1,
      generateProxy(args) -> 1,
    )
    val all = targetCondStr match
      case Some(str) => (generateString(str, args) -> 1) :: candidates
      case None      => candidates
    val chosen = weightedChoose(all)
    // re-parse at the requested production level
    cfg
      .esParser(prodName, args)
      .from(chosen.toString(grammar = Some(cfg.grammar)))
      .asInstanceOf[Syntactic]

  /** choose a property name relevant to the target function */
  def chooseProp: String =
    val props = targetFunc match
      case Some(func) =>
        val cands =
          if (randBool) reachableProps.getOrElse(func, Set())
          else specProps.getOrElse(func, Set())
        if (cands.nonEmpty) cands else allProps
      case None => allProps
    choose(props)

  /** choose a Proxy trap relevant to the target function */
  def chooseTrap: String =
    val traps = targetFunc match
      case Some(func) =>
        val cands =
          if (randBool) reachableTraps.getOrElse(func, Set())
          else specTraps.getOrElse(func, Set())
        if (cands.nonEmpty) cands else allTrapsSet
      case None => allTrapsSet
    choose(traps)

  // snippet generations

  def generateString(str: String, args: List[Boolean]): Syntactic = cfg
    .esParser(PRIMARY_EXPRESSION, args)
    .from(s"\\'$str\\'")
    .asInstanceOf[Syntactic]

  def generateObject(args: List[Boolean]): Syntactic =
    val k = chooseProp
    val v = choose(defaultValues)
    val raw = s"{ $k : $v }"
    cfg.esParser(PRIMARY_EXPRESSION, args).from(raw).asInstanceOf[Syntactic]

  def generateProxy(args: List[Boolean]): Syntactic =
    val trap = chooseTrap
    val target = if (fnProxyTraps.contains(trap)) "function ( ) { }" else "{}"
    val body = choose(proxyTrapBodies)
    val raw = s"(new Proxy($target, { $trap ( ) { $body } }))"
    cfg.esParser(PRIMARY_EXPRESSION, args).from(raw).asInstanceOf[Syntactic]

  def generateAccessor(args: List[Boolean]): Syntactic =
    val k = chooseProp
    val templates = List(
      s"{ get $k () {} }",
      s"{ get $k () { throw 0 ; } }",
      s"{ set $k (_) {} }",
      s"{ set $k (_) { throw 0 ; } }",
    )
    cfg
      .esParser(PRIMARY_EXPRESSION, args)
      .from(choose(templates))
      .asInstanceOf[Syntactic]

  // spec analyses

  lazy val specProps: Map[Func, Set[String]] = {
    val acc = MMap[Func, Set[String]]().withDefaultValue(Set())
    object PropFinder extends esmeta.ir.util.UnitWalker {
      var currentFunc: Option[Func] = None
      def addIfProp(e: Expr): Unit = for {
        func <- currentFunc
      } e match
        case EStr(str) => acc.update(func, acc(func) + str)
        case ERef(Field(Global("SYMBOL"), EStr(sym))) =>
          acc.update(func, acc(func) + s"[ Symbol . $sym ]")
        case _ => ()
      override def walk(inst: Inst) = inst match
        case ICall(_, EClo(name, _), as) if propReadingAlgos.contains(name) =>
          as.foreach(addIfProp)
        case _ => super.walk(inst)
    }
    for (cfgFunc <- cfg.funcs) {
      PropFinder.currentFunc = Some(cfgFunc)
      PropFinder.walk(cfgFunc.irFunc.body)
      PropFinder.currentFunc = None
    }
    acc.toMap
  }

  lazy val allProps: Set[String] = specProps.values.flatten.toSet

  def getReachableFuncs(root: Func): Set[Func] =
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

  lazy val reachableProps: Map[Func, Set[String]] = (for {
    (func, _) <- specProps
    reachable = getReachableFuncs(func)
    props = reachable.flatMap(specProps.getOrElse(_, Set()))
  } yield func -> props).toMap

  lazy val specTraps: Map[Func, Set[String]] = {
    val acc = MMap[Func, Set[String]]().withDefaultValue(Set())
    object TrapFinder extends esmeta.ir.util.UnitWalker {
      var currentFunc: Option[Func] = None
      override def walk(inst: Inst) = inst match
        case ICall(_, EClo(name, _), _) if trapAlgos.contains(name) =>
          for (func <- currentFunc)
            val trap = trapAlgos(name)
            acc.update(func, acc(func) + trap)
        case _ => super.walk(inst)
    }
    for (cfgFunc <- cfg.funcs) {
      TrapFinder.currentFunc = Some(cfgFunc)
      TrapFinder.walk(cfgFunc.irFunc.body)
      TrapFinder.currentFunc = None
    }
    acc.toMap
  }

  lazy val allTrapsSet: Set[String] = (objectProxyTraps ++ fnProxyTraps).toSet

  lazy val reachableTraps: Map[Func, Set[String]] = (for {
    (func, _) <- specTraps
    reachableFuncs = getReachableFuncs(func)
    traps = reachableFuncs.map(specTraps.getOrElse(_, Set())).flatten
  } yield func -> traps).toMap
}

object SpecStringSynthesizer {
  val PRIMARY_EXPRESSION = "PrimaryExpression"

  val propReadingAlgos = Set(
    "Get",
    "GetMethod",
    "HasOwnProperty",
    "HasProperty",
    "OrdinaryGetOwnProperty",
  )

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
    "OrdinaryGetPrototypeOf" -> "getPrototypeOf",
    "OrdinarySetPrototypeOf" -> "setPrototypeOf",
    "IsExtensible" -> "isExtensible",
    "OrdinaryIsExtensible" -> "isExtensible",
    "OrdinaryPreventExtensions" -> "preventExtensions",
    "TestIntegrityLevel" -> "isExtensible",
    "SetIntegrityLevel" -> "preventExtensions",
    "Call" -> "apply",
    "Construct" -> "construct",
  )

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

  val proxyTrapBodies: List[String] = List(
    "throw 0 ;",
    "",
    "return true ;",
    "return false ;",
    "return null ;",
    "return 0 ;",
    "return { } ;",
    "return [ ] ;",
  )

  private val primitives =
    List("null", "undefined", "true", "false", "0", "''", "Symbol ( )")
  private val callables = List(
    "function ( x ) { }",
    "function * ( x ) { }",
    "async function ( x ) { }",
    "async function * ( x ) { }",
    "( ) => { throw 0 ; }",
  )
  private val objects = List("{}", "[]")
  private val iterators = List(
    "{ next ( ) { return { done : true , value : 0 } ; } }",
    "{ next ( ) { throw 0 ; } }",
  )
  private val thenables = List(
    "{ then ( r ) { r ( 0 ) ; } }",
    "{ then ( ) { throw 0 ; } }",
  )
  val defaultValues: List[String] =
    primitives ++ callables ++ objects ++ iterators ++ thenables

  def findCondStr(e: Expr): Option[String] = e match
    case EBinary(BOp.Eq, EStr(str), _) => Some(str)
    case EBinary(BOp.Eq, _, EStr(str)) => Some(str)
    case _                             => None
}
