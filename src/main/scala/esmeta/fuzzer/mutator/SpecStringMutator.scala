package esmeta.fuzzer.mutator

import esmeta.cfg.{CFG, Func, Call}
import esmeta.es.*
import esmeta.es.util.*
import esmeta.fuzzer.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.util.BaseUtils.*

/** A mutator that generates based on strings in spec literals */
class SpecStringMutator(using cfg: CFG) extends Mutator {
  import Mutator.*, SpecStringMutator.*, Coverage.*

  val randomMutator = RandomMutator()

  val names = "SpecStringMutator" :: randomMutator.names

  /** mutate ASTs */
  def apply(
    ast: Ast,
    n: Int,
    target: Option[(CondView, Coverage)],
  ): Seq[Ast] =
    // count the number of primary expressions
    val k = primaryCounter(ast)
    if (k > 0) {
      targetFunc = None
      targetCondStr = None
      for ((cv, _) <- target)
        targetFunc = cfg.funcOf.get(cv.cond.branch)
        targetCondStr = findCondStr(cv.cond.branch.cond)
      Seq.tabulate(n)(_ => walk(ast))
    } else randomMutator(ast, n, target)

  /** function where target branch is in */
  private var targetFunc: Option[Func] = None

  /** string in target branch */
  private var targetCondStr: Option[String] = None

  /** choose a property name relevant to the target function */
  private def chooseProp: String =
    val props = targetFunc match
      case Some(func) =>
        val cands =
          if (randBool) reachableProps.getOrElse(func, Set())
          else specProps.getOrElse(func, Set())
        if (cands.nonEmpty) cands else allProps
      case None => allProps
    choose(props)

  /** choose a Proxy trap relevant to the target function */
  private def chooseTrap: String =
    val traps = targetFunc match
      case Some(func) =>
        val cands =
          if (randBool) reachableTraps.getOrElse(func, Set())
          else specTraps.getOrElse(func, Set())
        if (cands.nonEmpty) cands else allTrapsSet
      case None => allTrapsSet
    choose(traps)

  /** walk AST and return mutated AST */
  private def walk(ast: Ast): Ast = ast match
    case syn: Syntactic if isPrimary(syn) =>
      val candidates = List(
        generateObjectWithWeight(syn.args),
        generateGetterWithWeight(syn.args),
        generateSetterWithWeight(syn.args),
        generateProxyWithWeight(syn.args),
        syn -> 1,
      )
      if (targetCondStr.isDefined)
        val candidate = (generateString(targetCondStr.get, syn.args) -> 1)
        weightedChoose(candidate :: candidates)
      else weightedChoose(candidates)
    case Syntactic(name, args, rhsIdx, children) =>
      val newChildren = children.map {
        case Some(child) => Some(walk(child))
        case None        => None
      }
      Syntactic(name, args, rhsIdx, newChildren)
    case lex: Lexical => lex

  // convert the given string to primary expression
  def generateString(str: String, args: List[Boolean]): Syntactic = cfg
    .esParser(PRIMARY_EXPRESSION, args)
    .from(s"\'$str\'")
    .asInstanceOf[Syntactic]

  // Properties appearing in specification
  lazy val specProps: Map[Func, Set[String]] = {
    var acc: Map[Func, Set[String]] = Map()
    object PropFinder extends esmeta.ir.util.UnitWalker {
      var currentFunc: Option[Func] = None
      def addIfProp(e: Expr): Unit = for {
        func <- currentFunc
      } e match
        case EStr(str) =>
          acc += (func -> (acc.getOrElse(func, Set()) + str))
        case ERef(Field(Global("SYMBOL"), EStr(sym))) =>
          acc += (
            func -> (acc.getOrElse(func, Set()) + s"[ Symbol . $sym ]")
          )
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

  // Proxy traps relevant to each function (based on spec algorithms called)
  lazy val specTraps: Map[Func, Set[String]] = {
    var acc: Map[Func, Set[String]] = Map()
    object TrapFinder extends esmeta.ir.util.UnitWalker {
      var currentFunc: Option[Func] = None
      override def walk(inst: Inst) = inst match
        case ICall(_, EClo(name, _), _) if trapAlgos.contains(name) =>
          for (func <- currentFunc)
            val trap = trapAlgos(name)
            acc += (func -> (acc.getOrElse(func, Set()) + trap))
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

  // generate a random object, whose property is read in specification
  def generateObjectWithWeight(args: List[Boolean]): (Syntactic, Int) =
    val k = chooseProp
    val v = choose(defaultValues)
    val raw = s"{ $k : $v }"
    cfg.esParser(PRIMARY_EXPRESSION, args).from(raw).asInstanceOf[Syntactic] ->
    CATEGORY_WEIGHT

  // generate a Proxy for internal method interception
  def generateProxyWithWeight(args: List[Boolean]): (Syntactic, Int) =
    val trap = chooseTrap
    val target = if (fnProxyTraps.contains(trap)) "function ( ) { }" else "{}"
    val body = choose(proxyTrapBodies)
    val raw = s"(new Proxy($target, { $trap ( ) { $body } }))"
    cfg.esParser(PRIMARY_EXPRESSION, args).from(raw).asInstanceOf[Syntactic] ->
    CATEGORY_WEIGHT

  // generate a random getter/setter, whose property is read in specification
  def generateGetterWithWeight(args: List[Boolean]): (Syntactic, Int) =
    val k = chooseProp
    val getter = s"{ get $k () {} }"
    val throwingGetter = s"{ get $k () { throw 0 ; } }"
    cfg
      .esParser(PRIMARY_EXPRESSION, args)
      .from(choose(List(getter, throwingGetter)))
      .asInstanceOf[Syntactic] -> ACCESSOR_WEIGHT
  def generateSetterWithWeight(args: List[Boolean]): (Syntactic, Int) =
    val k = chooseProp
    val setter = s"{ set $k (_) {} }"
    val throwingSetter = s"{ set $k (_) { throw 0 ; } }"
    cfg
      .esParser(PRIMARY_EXPRESSION, args)
      .from(choose(List(setter, throwingSetter)))
      .asInstanceOf[Syntactic] -> ACCESSOR_WEIGHT
}

object SpecStringMutator {
  // macro
  val PRIMARY_EXPRESSION = "PrimaryExpression"

  // count the number of primaryExpressions
  def isPrimary(ast: Ast): Boolean = ast match
    case Syntactic(PRIMARY_EXPRESSION, _, _, _) => true
    case _                                      => false

  val primaryCounter = Util.AstCounter(isPrimary)

  // manually selected algorithms, whose purpose is reading property
  val propReadingAlgos = Set(
    "Get",
    "GetMethod",
    "HasOwnProperty",
    "HasProperty",
    "OrdinaryGetOwnProperty",
  )

  // category weights: object, accessor (getter+setter), proxy are equal
  val CATEGORY_WEIGHT = 2
  val ACCESSOR_WEIGHT = 1 // getter + setter = 2 = CATEGORY_WEIGHT

  // mapping from spec algorithms to corresponding Proxy traps
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

  // Proxy traps for object targets (internal methods only Proxy can intercept)
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

  // Proxy traps requiring function target
  val fnProxyTraps: List[String] = List("apply", "construct")

  // possible Proxy trap bodies
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

  // default value of property
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

  // find string literal in condition
  def findCondStr(e: Expr): Option[String] = e match
    case EBinary(BOp.Eq, EStr(str), _) => Some(str)
    case EBinary(BOp.Eq, _, EStr(str)) => Some(str)
    case _                             => None
}
