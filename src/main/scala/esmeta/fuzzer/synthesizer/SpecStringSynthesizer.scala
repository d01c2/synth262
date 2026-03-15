package esmeta.fuzzer.synthesizer

import esmeta.cfg.*
import esmeta.es.*
import esmeta.es.util.*
import esmeta.ir.{Func => IRFunc, *}
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Map => MMap}

/** A spec string synthesizer that wraps a base synthesizer */
class SpecStringSynthesizer(val base: Synthesizer)(using cfg: CFG)
  extends Synthesizer {
  import Coverage.*, SpecStringSynthesizer.*

  def name: String = "SpecStringSynthesizer"

  var targetCond: Option[Cond] = None

  private def targetFunc: Option[Func] =
    targetCond.flatMap(c => cfg.funcOf.get(c.branch))
  private def targetCondStr: Option[String] =
    targetCond.flatMap(c => findCondStr(c.branch.cond))

  def provenance: Option[Provenance] = targetCond.flatMap(findProvenance)

  private def findProvenance(cond: Cond): Option[Provenance] =
    val Cond(branch, targetSide) = cond
    if (findCondStr(branch.cond).isDefined) None // direct string equality
    else
      for {
        func <- cfg.funcOf.get(branch)
        (condVar, side) <- condRefVar(branch.cond, targetSide)
        call <- findDefCall(func, branch, condVar)
        result <- call match
          case ICall(_, EClo(algoName, _), _ :: EStr(prop) :: _)
              if propReadingAlgos.contains(algoName) =>
            Some(Provenance(algoName, Some(prop), side))
          case _ => None
      } yield result

  /** for syntactic production */
  def apply(
    name: String,
    args: List[Boolean],
    rhsIdx: Option[Int] = None,
  ): Syntactic =
    try { generateOne(name, args) }
    catch { case _: Exception => base(name, args, rhsIdx) }

  /** for lexical production */
  def apply(name: String): Lexical = base(name)

  /** Blind spec string generation */
  def generateOne(prodName: String, args: List[Boolean]): Syntactic =
    val candidates = List(
      generateObject(args) -> 2,
      generateGetter(args) -> 1,
      generateSetter(args) -> 1,
      generateProxy(args) -> 2,
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

  def generateString(str: String, args: List[Boolean]): Syntactic = cfg
    .esParser(PRIMARY_EXPRESSION, args)
    .from(s"\\'$str\\'")
    .asInstanceOf[Syntactic]

  def generateObject(args: List[Boolean]): Syntactic =
    val k = chooseProp
    val v = choose(defaultValues)
    val raw = s"{ $k : $v }"
    cfg.esParser(PRIMARY_EXPRESSION, args).from(raw).asInstanceOf[Syntactic]

  def generateProxy(
    args: List[Boolean],
    trapHint: Option[String] = None,
    targetAst: Option[Syntactic] = None,
  ): Syntactic =
    val trap = trapHint.getOrElse(chooseTrap)
    val needsCallable = fnProxyTraps.contains(trap)
    val target = targetAst match
      case Some(ast) if !needsCallable && objectLikeProds.contains(ast.name) =>
        ast.toString(grammar = Some(cfg.grammar))
      case _ => if needsCallable then "function ( ) { }" else "{}"
    val body = choose(proxyTrapBodies)
    val raw = s"(new Proxy($target, { $trap ( ) { $body } }))"
    cfg.esParser(PRIMARY_EXPRESSION, args).from(raw).asInstanceOf[Syntactic]

  private def generateAccessor(
    kind: String,
    params: String,
    args: List[Boolean],
    propHint: Option[String] = None,
  ): Syntactic =
    val k = propHint.getOrElse(chooseProp)
    val templates = List(
      s"{ $kind $k $params {} }",
      s"{ $kind $k $params { throw 0 ; } }",
    )
    cfg
      .esParser(PRIMARY_EXPRESSION, args)
      .from(choose(templates))
      .asInstanceOf[Syntactic]

  def generateGetter(
    args: List[Boolean],
    propHint: Option[String] = None,
  ): Syntactic = generateAccessor("get", "()", args, propHint)

  def generateSetter(
    args: List[Boolean],
    propHint: Option[String] = None,
  ): Syntactic = generateAccessor("set", "(_)", args, propHint)

  /** guided mutation */

  // wrap an existing AST in a Proxy. Returns None if AST is not object-like
  def wrapProxy(
    args: List[Boolean],
    trap: String,
    target: Syntactic,
  ): Option[Syntactic] =
    if (!objectLikeProds.contains(target.name)) None
    else
      try { Some(generateProxy(args, Some(trap), Some(target))) }
      catch { case _: Exception => None }

  // remove a specific property from an existing object literal
  def ejectProp(
    prop: String,
    args: List[Boolean],
    from: Syntactic,
  ): Option[Syntactic] =
    val props = getProps(from)
    if (props.isEmpty) None
    else
      val filtered = props.filterNot(propDef => propKey(propDef).contains(prop))
      if (filtered.length == props.length) None
      else Some(withProps(filtered, from.args))

  // inject a data property into an existing object literal
  def injectProp(
    prop: String,
    args: List[Boolean],
    into: Syntactic,
    values: List[String],
  ): Option[Syntactic] =
    val v = choose(values)
    injectPropDef(s"$prop : $v", args, Some(into))

  def injectGetter(
    args: List[Boolean],
    propHint: Option[String] = None,
    into: Option[Syntactic] = None,
    bodies: List[String],
  ): Option[Syntactic] =
    injectAccessor("get", "()", args, propHint, into, bodies)

  def injectMethod(
    args: List[Boolean],
    propHint: Option[String] = None,
    into: Option[Syntactic] = None,
    bodies: List[String],
  ): Option[Syntactic] =
    val k = propHint.getOrElse(chooseProp)
    val body = choose(bodies)
    injectPropDef(s"$k ( ) { $body }", args, into)

  /** inject a raw property definition string into an ObjectLiteral */
  private def injectPropDef(
    propDef: String,
    args: List[Boolean],
    into: Option[Syntactic],
  ): Option[Syntactic] = try {
    val parsed = cfg
      .esParser(PRIMARY_EXPRESSION, args)
      .from(s"{ $propDef }")
      .asInstanceOf[Syntactic]
    for {
      obj <- findObjectLiteral(parsed)
      propDef <- getProps(obj).headOption
      result <- into match
        case Some(target: Syntactic) if target.name == "ObjectLiteral" =>
          Some(withProps(getProps(target) :+ propDef, target.args))
        case None => Some(withProps(List(propDef), args))
        case _    => None
    } yield result
  } catch { case _: Exception => None }

  private def injectAccessor(
    kind: String,
    params: String,
    args: List[Boolean],
    propHint: Option[String],
    into: Option[Syntactic],
    bodies: List[String],
  ): Option[Syntactic] =
    val k = propHint.getOrElse(chooseProp)
    val body = choose(bodies)
    injectPropDef(s"$kind $k $params { $body }", args, into)

  /** ObjectLiteral AST manipulation */

  private def getProps(obj: Syntactic): List[Ast] = obj match
    case Syntactic("ObjectLiteral", _, 1 | 2, children) =>
      flattenPropList(children(0).get)
    case _ => Nil

  private def withProps(props: List[Ast], args: List[Boolean]): Syntactic =
    if (props.isEmpty) Syntactic("ObjectLiteral", args, 0, Vector())
    else
      val propDefs = buildPropList(props, args)
      Syntactic("ObjectLiteral", args, 1, Vector(Some(propDefs)))

  private def flattenPropList(pdl: Ast): List[Ast] = pdl match
    case Syntactic("PropertyDefinitionList", _, 0, children) =>
      children(0).toList
    case Syntactic("PropertyDefinitionList", _, 1, children)
        if children(0).isDefined =>
      children(0).toList.flatMap(flattenPropList) ++ children(1).toList
    case _ => Nil

  private def buildPropList(props: List[Ast], args: List[Boolean]): Syntactic =
    val (rhsIdx, children) =
      if (props.init.isEmpty) (0, Vector(Some(props.last)))
      else (1, Vector(Some(buildPropList(props.init, args)), Some(props.last)))
    Syntactic("PropertyDefinitionList", args, rhsIdx, children)

  private def findObjectLiteral(ast: Ast): Option[Syntactic] = ast match
    case s @ Syntactic("ObjectLiteral", _, _, _) => Some(s)
    case Syntactic(_, _, _, children) =>
      children.flatten.flatMap(findObjectLiteral).headOption
    case _ => None

  private def propKey(pd: Ast): Option[String] = pd match
    case Syntactic("PropertyDefinition", _, 0, children) =>
      children(0).map(_.toString(grammar = Some(cfg.grammar)).trim)
    case Syntactic(_, _, _, children) =>
      children.flatten.collectFirst {
        case s @ Syntactic("LiteralPropertyName", _, _, cs) =>
          cs(0).map(_.toString(grammar = Some(cfg.grammar)).trim)
      }.flatten
    case _ => None

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
    val cands = targetFunc match
      case Some(func) =>
        val s =
          if (randBool) reachable.getOrElse(func, Set())
          else spec.getOrElse(func, Set())
        if (s.isEmpty) all else s
      case None => all
    choose(cands)

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

  val PRIMARY_EXPRESSION = "PrimaryExpression"

  val propReadingAlgos = Set(
    "Get",
    "GetV",
    "GetMethod",
    "Invoke",
    "OrdinaryGet",
    "HasProperty",
    "OrdinaryHasProperty",
    "HasOwnProperty",
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

  /** productions that always evaluate to an object */
  val objectLikeProds: Set[String] = Set(
    "ObjectLiteral",
    "ArrayLiteral",
    "FunctionExpression",
    "GeneratorExpression",
    "AsyncFunctionExpression",
    "AsyncGeneratorExpression",
    "ArrowFunction",
    "AsyncArrowFunction",
    "ClassDeclaration",
    "ClassExpression",
    "RegularExpressionLiteral",
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

  // value categories

  val falsyValues: List[String] = List("null", "undefined", "false", "0", "''")

  val truthyValues: List[String] = List(
    "true",
    "1",
    "Symbol ( )",
    "function ( x ) { }",
    "( ) => { }",
    "{}",
    "[]",
  )

  val callableValues: List[String] = List(
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
    falsyValues ++ truthyValues ++ callableValues ++ objects ++
    iterators ++ thenables

  // categories for accessors/methods

  val truthyBodies: List[String] =
    List("return 1 ;", "return true ;", "return { } ;")

  val falsyBodies: List[String] =
    List("", "return null ;", "return 0 ;", "return false ;")

  val abruptBodies: List[String] = List("throw 0 ;")

  // helper for finding provenance

  def findCondStr(e: Expr): Option[String] = e match
    case EBinary(BOp.Eq, EStr(str), _) => Some(str)
    case EBinary(BOp.Eq, _, EStr(str)) => Some(str)
    case _                             => None

  case class Provenance(
    algoName: String,
    propHint: Option[String],
    side: Boolean,
  )

  /** extract variable reference and side from a branch */
  def condRefVar(expr: Expr, cond: Boolean): Option[(Local, Boolean)] =
    expr match
      case EBinary(BOp.Eq, ERef(v: Local), EBool(b)) => Some((v, cond == b))
      case EBinary(BOp.Eq, EBool(b), ERef(v: Local)) => Some((v, cond == b))
      case ERef(v: Local)                            => Some((v, cond))
      case _                                         => None

  /** Find the CallInst that defines a variable by walking predecessors */
  def findDefCall(
    func: Func,
    from: Node,
    target: Local,
    visited: Set[Node] = Set(),
  ): Option[CallInst] =
    if (visited.contains(from)) None
    else
      val seen = visited + from
      func.preds(from).foldLeft(Option.empty[CallInst]) {
        case (found @ Some(_), _) => found
        case (None, call: Call) if call.callInst.lhs == target =>
          Some(call.callInst)
        case (None, call: Call) => findDefCall(func, call, target, seen)
        case (None, block: Block) =>
          block.insts.reverseIterator.collectFirst {
            case ILet(lhs, expr) if lhs == target => expr
          } match
            case Some(ERef(alias: Local)) =>
              findDefCall(func, block, alias, seen)
            case Some(_) => None
            case None    => findDefCall(func, block, target, seen)
        case (None, branch: Branch) => findDefCall(func, branch, target, seen)
      }
}
