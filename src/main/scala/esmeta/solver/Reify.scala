package esmeta.solver

import esmeta.cfg.Func
import esmeta.ir.*
import esmeta.spec.{BuiltinHead, BuiltinPath}
import esmeta.ty.*
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Set => MSet}
import Formula.*, Term.*

/** reify simplified formulas into JS code for entry parameters */
case class Reify(formulas: List[Formula], entryParams: List[String]) {
  import Reify.*

  def witness: Option[Witness] =
    if (hasUninterpretableApp(formulas)) None
    else {
      // normalize equation order
      val normalized = formulas.map(normalizeEq)
      // filter relevant formulas for each param and build witness
      val pairs = entryParams.map { param =>
        val relevants = normalized.filter(_.freeVars.contains(param))
        buildExpr(param, relevants).map(param -> _)
      }
      // all params must succeed for a valid witness
      if (pairs.forall(_.isDefined)) Some(pairs.flatten.toMap)
      else None
    }

  private def buildExpr(param: String, fs: List[Formula]): Option[String] =
    val consumed = MSet[Formula]()

    // literal equality
    val litVal = fs.collectFirst {
      case f @ FEq(TVar(_), TLit(lit)) => consumed += f; lit
    }

    // narrow type from all type constraints
    val narrowedTy = fs.foldLeft(ESValueT) {
      case (ty, f @ FEq(TTypeOf(TVar(_)), TType(pos))) =>
        consumed += f; ty && pos
      case (ty, f @ FNot(FEq(TTypeOf(TVar(_)), TType(neg)))) =>
        consumed += f; ty -- neg
      case (ty, _) => ty
    }
    val hasTyConstraint = narrowedTy != ESValueT

    // property constraints from Get/HasProperty
    val propsValue = fs.collect {
      case f @ FEq(TApp("Get", List(_, TLit(EStr(key)))), TLit(lit)) =>
        consumed += f; (key, lit)
    }.toMap
    val propsAbrupt = fs.collect {
      case f @ FEq(TTypeOf(TApp("Get", List(_, TLit(EStr(key))))), TType(ty))
          if ty <= AbruptT =>
        consumed += f; key
    }.toSet
    val propsExist = fs.collect {
      case f @ FEq(
            TApp("HasProperty", List(_, TLit(EStr(key)))),
            TLit(EBool(exists)),
          ) =>
        consumed += f; (key, exists)
      case f @ FExists(TVar(_), field) =>
        consumed += f; (field, true)
      case f @ FNot(FExists(TVar(_), field)) =>
        consumed += f; (field, false)
    }.toMap

    // object config from IsExtensible/GetPrototypeOf
    val extensible = fs.collectFirst {
      case f @ FEq(TApp("IsExtensible", _), TLit(EBool(false))) =>
        consumed += f; false
      case f @ FEq(TApp("IsExtensible", _), TLit(EBool(true))) =>
        consumed += f; true
    }
    val prototype = fs.collectFirst {
      case f @ FEq(TApp("GetPrototypeOf", _), TLit(lit)) =>
        consumed += f; lit
    }

    // disequality constraints
    val excluded = fs.collect {
      case f @ FNot(FEq(TVar(_), TLit(lit))) => consumed += f; lit
    }

    // interval bounds from FLt constraints: [lo, hi]
    var lo: Option[BigDecimal] = None
    var hi: Option[BigDecimal] = None
    for (f <- fs) f match
      case f @ FLt(TVar(_), TLit(EMath(k))) =>
        consumed += f; hi = Some(hi.fold(k - 1)(_ min (k - 1)))
      case f @ FLt(TLit(EMath(k)), TVar(_)) =>
        consumed += f; lo = Some(lo.fold(k + 1)(_ max (k + 1)))
      case f @ FNot(FLt(TVar(_), TLit(EMath(k)))) =>
        consumed += f; lo = Some(lo.fold(k)(_ max k))
      case f @ FNot(FLt(TLit(EMath(k)), TVar(_))) =>
        consumed += f; hi = Some(hi.fold(k)(_ min k))
      case _ => ()
    val hasInterval = lo.isDefined || hi.isDefined
    val excMath = excluded.collect { case EMath(n) => n }.toSet
    val intervalPick: Option[BigDecimal] =
      if (!hasInterval) None
      else {
        val l = lo.getOrElse(BigDecimal(0))
        val h = hi.getOrElse(l)
        if (l > h) None
        else
          Iterator
            .iterate(l)(_ + 1)
            .takeWhile(_ <= h)
            .find(!excMath.contains(_))
      }

    val unconsumed = fs.filterNot(consumed)

    val hasProps = propsValue.nonEmpty || propsAbrupt.nonEmpty ||
      propsExist.exists(_._2)
    val hasObjConstraints =
      hasProps || extensible.isDefined || prototype.isDefined

    if (litVal.isDefined) litVal.flatMap(litToJs)
    else if (hasTyConstraint && narrowedTy.isBottom) None
    else if (unconsumed.nonEmpty) buildProxy(narrowedTy, unconsumed)
    else if (hasObjConstraints)
      buildObject(
        narrowedTy,
        propsValue,
        propsAbrupt,
        propsExist,
        extensible,
        prototype,
      )
    else if (hasInterval) intervalPick.flatMap(n => litToJs(EMath(n)))
    else if (hasTyConstraint || excluded.nonEmpty)
      if (narrowedTy <= ObjectT)
        buildObject(narrowedTy, Map(), Set(), Map(), None, None)
      else defaultFor(narrowedTy, excluded.toSet)
    else Some("undefined")

  // build plain object from property + config constraints
  private def buildObject(
    ty: ValueTy,
    propsValue: Map[String, LiteralExpr],
    propsAbrupt: Set[String],
    propsExist: Map[String, Boolean],
    extensible: Option[Boolean],
    prototype: Option[LiteralExpr],
  ): Option[String] = recordFactory(ty).map { base =>
    val entries = List.newBuilder[String]
    for ((key, lit) <- propsValue)
      litToJs(lit).foreach(jsLit => entries += s"$key: $jsLit")
    for (key <- propsAbrupt)
      entries += s"get $key() { throw 0; }"
    for ((key, exists) <- propsExist)
      if (exists && !propsValue.contains(key) && !propsAbrupt.contains(key))
        entries += s"$key: 0"

    val propList = entries.result()
    val objLiteral =
      if (propList.isEmpty) base else s"{${propList.mkString(", ")}}"

    (extensible, prototype) match
      case (Some(false), _)   => s"Object.preventExtensions($objLiteral)"
      case (_, Some(ENull())) => "Object.create(null)"
      case _                  => objLiteral
  }

  // build Proxy from unhandled trap formulas
  private def buildProxy(
    ty: ValueTy,
    trapFormulas: List[Formula],
  ): Option[String] =
    val target = trapFormulas
      .collectFirst {
        case FEq(TTypeOf(TApp(fname, _)), TType(_))       => proxyTarget(fname)
        case FEq(TApp(fname, _), _)                       => proxyTarget(fname)
        case FNot(FEq(TApp(fname, _), _))                 => proxyTarget(fname)
        case FNot(FEq(TTypeOf(TApp(fname, _)), TType(_))) => proxyTarget(fname)
      }
      .getOrElse("{}")

    val traps = List.newBuilder[(String, String)]
    for (formula <- trapFormulas) formula match
      case FEq(TTypeOf(TApp(fname, _)), TType(ty)) if ty <= AbruptT =>
        proxyTrapName.get(fname).foreach(trap => traps += trap -> "throw 0;")
      case FEq(TApp(fname, _), TLit(lit)) =>
        for {
          jsLit <- litToJs(lit)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsLit;"
      case FNot(FEq(TApp(fname, _), TLit(lit))) =>
        proxyTrapName
          .get(fname)
          .foreach(trap =>
            traps += trap -> s"return ${defaultFor(ESValueT, Set(lit))};",
          )
      case FEq(TTypeOf(TApp(fname, _)), TType(ty))
          if !(ty <= AbruptT) && !(ty <= NormalT) =>
        for {
          jsVal <- defaultFor(ty)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case FNot(FEq(TTypeOf(TApp(fname, _)), TType(ty)))
          if !(ty <= AbruptT) && !(ty <= NormalT) =>
        for {
          jsVal <- defaultFor(ESValueT -- ty)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case _ => ()

    val trapList = traps.result()
    if (trapList.isEmpty) return None

    val trapStr =
      trapList.map((name, body) => s"$name() { $body }").mkString(", ")
    Some(s"new Proxy($target, { $trapStr })")
}

object Reify {
  private val proxyTrapName: Map[String, String] = Map(
    "GetPrototypeOf" -> "getPrototypeOf",
    "SetPrototypeOf" -> "setPrototypeOf",
    "IsExtensible" -> "isExtensible",
    "PreventExtensions" -> "preventExtensions",
    "GetOwnProperty" -> "getOwnPropertyDescriptor",
    "DefineOwnProperty" -> "defineProperty",
    "HasProperty" -> "has",
    "Get" -> "get",
    "Set" -> "set",
    "Delete" -> "deleteProperty",
    "OwnPropertyKeys" -> "ownKeys",
    "Call" -> "apply",
    "Construct" -> "construct",
  )

  val internalMethods: Set[String] = proxyTrapName.keySet

  def isInternalMethod(fname: String): Boolean =
    internalMethods.contains(fname)

  private def proxyTarget(fname: String): String = fname match
    case "Call"      => "() => {}"
    case "Construct" => "function(){}"
    case _           => "{}"

  private def litToJs(lit: LiteralExpr): Option[String] = lit match
    case EBool(b) => Some(b.toString)
    case EStr(s)  => Some(s"\"$s\"")
    case EMath(n) =>
      Some(if (n.isWhole) n.toBigInt.toString else n.toString)
    case ENumber(d) =>
      if (d.isNaN) Some("NaN")
      else if (d.isPosInfinity) Some("Infinity")
      else if (d.isNegInfinity) Some("-Infinity")
      else if (isNegZero(d)) Some("-0")
      else Some(d.toString)
    case EBigInt(n)     => Some(s"${n}n")
    case EInfinity(pos) => Some(if (pos) "Infinity" else "-Infinity")
    case ECodeUnit(c)   => Some(c.toInt.toString)
    case ENull()        => Some("null")
    case EUndef()       => Some("undefined")
    case _: EEnum       => None

  // ordered literal candidates per type; first non-excluded wins
  private val literalCandidates: List[(ValueTy, List[LiteralExpr])] = List(
    NumberT -> List(EMath(0), EMath(1)),
    StrT -> List(EStr(""), EStr("a")),
    BoolT -> List(EBool(true), EBool(false)),
    NullT -> List(ENull()),
    UndefT -> List(EUndef()),
    BigIntT -> List(EBigInt(0)),
  )

  // pick first value matching type and not excluded
  private def defaultFor(
    ty: ValueTy,
    excluded: Set[LiteralExpr] = Set(),
  ): Option[String] =
    // non-literal types (not excludable)
    if (!(ty && FunctionT).isBottom) Some("function(){}")
    else if (!(ty && ObjectT).isBottom) Some("{}")
    else if (!(ty && SymbolT).isBottom) Some("Symbol()")
    else
      literalCandidates.collectFirst {
        case (candidateTy, lits) if !(ty && candidateTy).isBottom =>
          lits.find(!excluded.contains(_)).flatMap(litToJs)
      }.flatten

  private def recordFactory(ty: ValueTy): Option[String] =
    if (ty <= ConstructorT) Some("function(){}")
    else if (ty <= FunctionT) Some("() => {}")
    else if (ty.record.names <= ObjectT.record.names) Some("{}")
    else None

  // normalize FEq so non-literal term is always on the left
  private def normalizeEq(f: Formula): Formula = f match
    case FEq(l: TLit, r) if !r.isInstanceOf[TLit]       => FEq(r, l)
    case FNot(FEq(l: TLit, r)) if !r.isInstanceOf[TLit] => FNot(FEq(r, l))
    case _                                              => f

  def hasUninterpretableApp(fs: List[Formula]): Boolean =
    def fromTerm(t: Term): Set[String] = t match
      case TApp(fname, args) => Set(fname) ++ args.flatMap(fromTerm)
      case TField(base, _)   => fromTerm(base)
      case TList(elems)      => elems.flatMap(fromTerm).toSet
      case TUOp(_, t)        => fromTerm(t)
      case TBOp(_, lhs, rhs) => fromTerm(lhs) ++ fromTerm(rhs)
      case TVOp(_, args)     => args.flatMap(fromTerm).toSet
      case TSizeOf(t)        => fromTerm(t)
      case TTypeOf(t)        => fromTerm(t)
      case _                 => Set()
    def fromFormula(f: Formula): Set[String] = f match
      case FNot(inner)   => fromFormula(inner)
      case FEq(l, r)     => fromTerm(l) ++ fromTerm(r)
      case FLt(l, r)     => fromTerm(l) ++ fromTerm(r)
      case FExists(b, _) => fromTerm(b)
    fs.exists(fromFormula(_).exists(!internalMethods.contains(_)))

  /** JS expression to access a builtin function */
  def funcAccessExpr(f: Func): Option[String] =
    f.head
      .collect { case h: BuiltinHead => h.path }
      .map(pathStr)
      .filter(_.nonEmpty)

  /** build a JS call that invokes the builtin with solved arguments */
  def toJsCall(func: Func, params: List[String], w: Witness): Option[String] =
    func.head.collect { case h: BuiltinHead => h }.flatMap { h =>
      val thisVal = w.getOrElse("this", "undefined")
      val newTarget = w.getOrElse("NewTarget", "undefined")
      val args = params
        .filterNot(p => p == "this" || p == "NewTarget")
        .map(p => w.getOrElse(p, "undefined"))
      h.path match
        case BuiltinPath.YetPath(_) => None
        case BuiltinPath.Getter(base) =>
          Some(s"${descriptorExpr(base)}.get.call($thisVal)")
        case BuiltinPath.Setter(base) =>
          val v = args.headOption.getOrElse("0")
          Some(s"${descriptorExpr(base)}.set.call($thisVal, $v)")
        case path =>
          val name = pathStr(path)
          if (newTarget != "undefined")
            Some(
              s"Reflect.construct($name, [${args.mkString(", ")}], $newTarget)",
            )
          else Some(s"$name.call(${(thisVal :: args).mkString(", ")})")
    }

  private def descriptorExpr(base: BuiltinPath): String = base match
    case BuiltinPath.NormalAccess(owner, prop) =>
      s"Object.getOwnPropertyDescriptor(${pathStr(owner)}, '$prop')"
    case BuiltinPath.SymbolAccess(owner, sym) =>
      s"Object.getOwnPropertyDescriptor(${pathStr(owner)}, Symbol.$sym)"
    case _ => "undefined"

  private def pathStr(path: BuiltinPath): String = path match
    case BuiltinPath.Base(name) => globalAlias.getOrElse(name, name)
    case BuiltinPath.NormalAccess(base, name) => s"${pathStr(base)}.$name"
    case BuiltinPath.SymbolAccess(base, sym) => s"${pathStr(base)}[Symbol.$sym]"
    case BuiltinPath.Getter(base)            => pathStr(base)
    case BuiltinPath.Setter(base)            => pathStr(base)
    case BuiltinPath.YetPath(_)              => ""

  private val globalAlias: Map[String, String] = Map(
    "TypedArray" -> "Object.getPrototypeOf(Int8Array)",
    "ArrayIteratorPrototype" -> "Object.getPrototypeOf([][Symbol.iterator]())",
    "AsyncFunction" -> "(async function(){}).constructor",
    "AsyncGeneratorFunction" -> "(async function*(){}).constructor",
    "AsyncGeneratorPrototype" -> "Object.getPrototypeOf(async function*(){}).prototype",
    "AsyncIteratorPrototype" -> "Object.getPrototypeOf(Object.getPrototypeOf(async function*(){}).prototype)",
    "AsyncFromSyncIteratorPrototype" -> "",
    "GeneratorFunction" -> "(function*(){}).constructor",
    "GeneratorPrototype" -> "Object.getPrototypeOf(function*(){}).prototype",
    "Iterator" -> "Iterator",
    "IteratorHelperPrototype" -> "Object.getPrototypeOf(Iterator.from([]).drop(0))",
    "MapIteratorPrototype" -> "Object.getPrototypeOf(new Map()[Symbol.iterator]())",
    "SetIteratorPrototype" -> "Object.getPrototypeOf(new Set()[Symbol.iterator]())",
    "StringIteratorPrototype" -> "Object.getPrototypeOf(''[Symbol.iterator]())",
    "RegExpStringIteratorPrototype" -> "Object.getPrototypeOf(/./[Symbol.matchAll](''))",
    "WrapForValidIteratorPrototype" -> "Object.getPrototypeOf(Iterator.from({[Symbol.iterator](){return{}}}))",
    "ThrowTypeError" -> """(function(){"use strict";return Object.getOwnPropertyDescriptor(arguments,"callee").get})()""",
  )
}
