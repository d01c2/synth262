package esmeta.solver

import esmeta.cfg.Func
import esmeta.ir.*
import esmeta.spec.{BuiltinHead, BuiltinPath}
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Set => MSet}
import Formula.*, Term.*

/** reify simplified formulas into JS code for entry parameters */
case class Reify(formulas: List[Formula], entryParams: List[String]) {
  import Reify.*

  def witness: Option[Witness] =
    if (hasUninterpretableApp(formulas)) None
    else {
      val normalized = formulas.map(normalizeEq)
      // params that must be absent (not passed) per __args__ constraints
      val omitted = normalized.collect {
        case FNot(FExists(TVar("__args__"), field)) => field
      }.toSet
      val activeParams = entryParams.filterNot(omitted)
      val pairs = activeParams.map { param =>
        val relevants = normalized.filter(_.freeVars.contains(param))
        buildExpr(param, relevants).map(param -> _)
      }
      if (pairs.forall(_.isDefined)) Some(pairs.flatten.toMap)
      else None
    }

  private def buildExpr(param: String, fs: List[Formula]): Option[String] =
    val consumed = MSet[Formula]()

    // literal equality
    val litVal = fs.collectFirst {
      case f @ FEq(TVar(_), TLit(lit)) => consumed += f; lit
    }

    // narrow type from type constraints and internal slot existence
    var ty = ESValueT
    for (f <- fs) f match
      case f @ FEq(TTypeOf(TVar(_)), TType(pos)) =>
        consumed += f; ty = ty && pos
      case f @ FNot(FEq(TTypeOf(TVar(_)), TType(neg))) =>
        consumed += f; ty = ty -- neg
      case f @ FExists(TVar(_), field) if fieldToRecordTy.contains(field) =>
        consumed += f; ty = ty && fieldToRecordTy(field)
      case f @ FNot(FExists(TVar(_), field))
          if fieldToRecordTy.contains(field) =>
        consumed += f; ty = ty -- fieldToRecordTy(field)
      case _ => ()
    val narrowedTy = ty
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
      case f @ FExists(TVar(_), field) if !fieldToRecordTy.contains(field) =>
        consumed += f; (field, true)
      case f @ FNot(FExists(TVar(_), field))
          if !fieldToRecordTy.contains(field) =>
        consumed += f; (field, false)
    }.toMap

    // typed property constraints — only when the base is an object literal
    // that can have properties merged into it
    val objLiteralBase = defaultFor(narrowedTy).exists(_.startsWith("{"))
    val propsTyped =
      if (objLiteralBase) fs.collect {
        case f @ FEq(TTypeOf(TApp("Get", List(_, TLit(EStr(key))))), TType(ty))
            if !(ty <= AbruptT) && !(ty <= NormalT) =>
          consumed += f; (key, ty)
      }.toMap
      else Map.empty[String, ValueTy]
    if (objLiteralBase) for (f <- fs) f match
      case f @ FNot(FEq(TApp("Get", List(_, TLit(EStr(_)))), TLit(_))) =>
        consumed += f
      case f @ FNot(
            FEq(TTypeOf(TApp("Get", List(_, TLit(EStr(_))))), TType(_)),
          ) =>
        consumed += f
      case _ => ()

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

    // interval bounds from FLt constraints
    // strict: (lo, hi), inclusive: [lo, hi]
    var loStrict: Option[BigDecimal] = None
    var hiStrict: Option[BigDecimal] = None
    var loIncl: Option[BigDecimal] = None
    var hiIncl: Option[BigDecimal] = None
    def numVal(lit: LiteralExpr): Option[BigDecimal] = lit match
      case EMath(n)                                => Some(n)
      case ENumber(d) if !d.isNaN && !d.isInfinite => Some(BigDecimal(d))
      case _                                       => None
    for (f <- fs) f match
      case f @ FLt(TVar(_), TLit(lit)) => // x < k
        numVal(lit).foreach(k => {
          consumed += f; hiStrict = Some(hiStrict.fold(k)(_ min k))
        })
      case f @ FLt(TLit(lit), TVar(_)) => // k < x
        numVal(lit).foreach(k => {
          consumed += f; loStrict = Some(loStrict.fold(k)(_ max k))
        })
      case f @ FNot(FLt(TVar(_), TLit(lit))) => // x >= k
        numVal(lit).foreach(k => {
          consumed += f; loIncl = Some(loIncl.fold(k)(_ max k))
        })
      case f @ FNot(FLt(TLit(lit), TVar(_))) => // k >= x
        numVal(lit).foreach(k => {
          consumed += f; hiIncl = Some(hiIncl.fold(k)(_ min k))
        })
      case _ => ()
    val hasInterval = loStrict.isDefined || hiStrict.isDefined ||
      loIncl.isDefined || hiIncl.isDefined
    val excSet = excluded.flatMap(numVal).toSet
    val intervalPick: Option[BigDecimal] =
      if (!hasInterval) None
      else
        def valid(v: BigDecimal): Boolean =
          !excSet.contains(v) &&
          loStrict.forall(_ < v) && hiStrict.forall(v < _) &&
          loIncl.forall(_ <= v) && hiIncl.forall(v <= _)
        // effective bounds for picking
        val effLo = List(loStrict, loIncl).flatten match
          case Nil => None
          case xs  => Some(xs.max)
        val effHi = List(hiStrict, hiIncl).flatten match
          case Nil => None
          case xs  => Some(xs.min)
        // single-point range
        val singlePick = for {
          l <- effLo; h <- effHi; if l <= h
        } yield (l + h) / 2
        // try integers in a bounded window
        val lo = effLo.getOrElse(effHi.getOrElse(BigDecimal(0)) - 100)
        val hi = effHi.getOrElse(effLo.getOrElse(BigDecimal(0)) + 100)
        val intLo = lo.setScale(0, BigDecimal.RoundingMode.CEILING)
        val intHi = hi.setScale(0, BigDecimal.RoundingMode.FLOOR)
        val intPick = Iterator
          .iterate(intLo)(_ + 1)
          .takeWhile(_ <= intHi)
          .take(200) // safety bound
          .find(valid)
        intPick.orElse {
          singlePick.filter(valid)
        }

    val unconsumed = fs.filterNot(consumed)

    val hasProps = propsValue.nonEmpty || propsAbrupt.nonEmpty ||
      propsTyped.nonEmpty || propsExist.exists(_._2)
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
        propsTyped,
        propsExist,
        extensible,
        prototype,
      )
    else if (hasInterval) intervalPick.flatMap(n => litToJs(EMath(n)))
    else if (hasTyConstraint || excluded.nonEmpty)
      if (narrowedTy <= ObjectT)
        buildObject(narrowedTy, Map(), Set(), Map(), Map(), None, None)
      else defaultFor(narrowedTy, excluded.toSet)
    else Some("undefined")

  // build plain object from property + config constraints
  private def buildObject(
    ty: ValueTy,
    propsValue: Map[String, LiteralExpr],
    propsAbrupt: Set[String],
    propsTyped: Map[String, ValueTy],
    propsExist: Map[String, Boolean],
    extensible: Option[Boolean],
    prototype: Option[LiteralExpr],
  ): Option[String] = defaultFor(ty).map { base =>
    val entries = List.newBuilder[String]
    for ((key, lit) <- propsValue)
      litToJs(lit).foreach(jsLit => entries += s"$key: $jsLit")
    for (key <- propsAbrupt)
      entries += s"get $key() { throw 0; }"
    for ((key, propTy) <- propsTyped)
      if (!propsValue.contains(key) && !propsAbrupt.contains(key))
        defaultFor(propTy).foreach(jsVal => entries += s"$key: $jsVal")
    for ((key, exists) <- propsExist)
      if (
        exists && !propsValue.contains(key) && !propsAbrupt.contains(key)
        && !propsTyped.contains(key)
      )
        entries += s"$key: 0"

    val propList = entries.result()
    val objLiteral =
      if (propList.isEmpty) base
      else
        val baseProps =
          if (base.startsWith("{") && base.endsWith("}"))
            val inner = base.drop(1).dropRight(1).trim
            if (inner.isEmpty) Nil else List(inner)
          else Nil
        s"{${(baseProps ++ propList).mkString(", ")}}"

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
        case FEq(TTypeOf(TApp(fname: String, _)), TType(_)) =>
          proxyTarget(fname)
        case FEq(TApp(fname: String, _), _)       => proxyTarget(fname)
        case FNot(FEq(TApp(fname: String, _), _)) => proxyTarget(fname)
        case FNot(FEq(TTypeOf(TApp(fname: String, _)), TType(_))) =>
          proxyTarget(fname)
      }
      .getOrElse("{}")

    val traps = List.newBuilder[(String, String)]
    for (formula <- trapFormulas) formula match
      case FEq(TTypeOf(TApp(fname: String, _)), TType(ty)) if ty <= AbruptT =>
        proxyTrapName.get(fname).foreach(trap => traps += trap -> "throw 0;")
      case FEq(TApp(fname: String, _), TLit(lit)) =>
        for {
          jsLit <- litToJs(lit)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsLit;"
      case FNot(FEq(TApp(fname: String, _), TLit(lit))) =>
        for {
          jsVal <- defaultFor(ESValueT, Set(lit))
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case FEq(TTypeOf(TApp(fname: String, _)), TType(ty))
          if !(ty <= AbruptT) && !(ty <= NormalT) =>
        for {
          jsVal <- defaultFor(ty)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case FNot(FEq(TTypeOf(TApp(fname: String, _)), TType(ty)))
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

  // specific record types (language-type only)
  private val specificDefaults: List[(ValueTy, String)] = List(
    RecordT("TypedArray") -> "new Int8Array()",
    RecordT("ArrayIteratorInstance") -> "[][Symbol.iterator]()",
    RecordT("RegExp") -> "{[Symbol.match]: true}",
    RecordT("BuiltinFunctionObject") -> "Array.isArray",
    RecordT("BooleanObject") -> "Object(true)",
    RecordT("NumberObject") -> "Object(0)",
    RecordT("BigIntObject") -> "Object(0n)",
    RecordT("StringExoticObject") -> "Object('')",
    RecordT("Map") -> "new Map()",
    RecordT("Set") -> "new Set()",
    RecordT("WeakMap") -> "new WeakMap()",
    RecordT("WeakSet") -> "new WeakSet()",
    RecordT("ArrayBuffer") -> "new ArrayBuffer(0)",
    RecordT("DataView") -> "new DataView(new ArrayBuffer(0))",
    RecordT("Date") -> "new Date()",
    RecordT("Promise") -> "new Promise(() => {})",
    RecordT("ErrorObject") -> "new Error()",
    RecordT("Generator") -> "(function*(){})()",
    RecordT("AsyncGenerator") -> "(async function*(){})()",
    RecordT("WeakRef") -> "new WeakRef({})",
    RecordT("FinalizationRegistry") -> "new FinalizationRegistry(() => {})",
  )

  // abstract types (primitives + general object categories)
  private val abstractDefaults: List[(ValueTy, String)] = List(
    ConstructorT -> "function(){}",
    FunctionT -> "() => {}",
    NumberT -> "0",
    StrT -> "\"\"",
    BoolT -> "true",
    NullT -> "null",
    UndefT -> "undefined",
    BigIntT -> "0n",
    SymbolT -> "Symbol()",
    ObjectT -> "{}",
  )

  // all candidates: specific first (for exact match)
  private val defaults = specificDefaults ++ abstractDefaults

  private def defaultFor(
    ty: ValueTy,
    excluded: Set[LiteralExpr] = Set(),
  ): Option[String] =
    val excJs = excluded.flatMap(litToJs)
    // 1. exact match
    defaults
      .collectFirst {
        case (ct, js) if (ty <= ct) && (ct <= ty) && !excJs(js) => js
      }
      .orElse {
        // 2. specific intersection for narrow object types
        if (ty <= ObjectT && !(ObjectT <= ty))
          specificDefaults.collectFirst {
            case (ct, js) if !(ty && ct).isBottom && !excJs(js) => js
          }
        else None
      }
      .orElse {
        // 3. abstract subtype match
        abstractDefaults.collectFirst {
          case (ct, js) if ty <= ct && !excJs(js) => js
        }
      }
      .orElse {
        // 4. abstract intersection match
        abstractDefaults.collectFirst {
          case (ct, js) if !(ty && ct).isBottom && !excJs(js) => js
        }
      }

  // reverse index: field name -> union of record types that have it
  private lazy val fieldToRecordTy: Map[String, ValueTy] =
    val tyModel = ManualInfo.tyModel
    val pairs = for {
      (name, _) <- tyModel.declMap.toList
      (field, binding) <- tyModel.fieldsOf(name)
      if !binding.absent
    } yield (field, name)
    pairs
      .groupMap(_._1)(_._2)
      .map { (field, names) =>
        field -> names.foldLeft(BotT: ValueTy)((ty, n) => ty || RecordT(n))
      }

  // normalize FEq so non-literal term is always on the left
  private def normalizeEq(f: Formula): Formula = f match
    case FEq(l: TLit, r) if !r.isInstanceOf[TLit]       => FEq(r, l)
    case FNot(FEq(l: TLit, r)) if !r.isInstanceOf[TLit] => FNot(FEq(r, l))
    case _                                              => f

  def hasUninterpretableApp(fs: List[Formula]): Boolean =
    def fromTerm(t: Term): Set[String] = t match
      case TApp(fname: String, args) => Set(fname) ++ args.flatMap(fromTerm)
      case TApp(_, args)             => args.flatMap(fromTerm).toSet
      case TField(base, _)           => fromTerm(base)
      case TList(elems)              => elems.flatMap(fromTerm).toSet
      case TRecord(_, fs)            => fs.values.flatMap(fromTerm).toSet
      case TMap(es)   => es.flatMap((k, v) => fromTerm(k) ++ fromTerm(v)).toSet
      case TTypeOf(t) => fromTerm(t)
      case _          => Set()
    def fromFormula(f: Formula): Set[String] = f match
      case FNot(inner)   => fromFormula(inner)
      case FEq(l, r)     => fromTerm(l) ++ fromTerm(r)
      case FLt(l, r)     => fromTerm(l) ++ fromTerm(r)
      case FExists(b, _) => fromTerm(b)
    fs.exists(fromFormula(_).exists(!internalMethods.contains(_)))

  def outerAppNames(f: Formula): Set[String] =
    def fromTerm(t: Term): Set[String] = t match
      case TApp(fname: String, _) if !internalMethods(fname) => Set(fname)
      case TApp(_, args)   => args.flatMap(fromTerm).toSet
      case TField(base, _) => fromTerm(base)
      case TList(elems)    => elems.flatMap(fromTerm).toSet
      case TRecord(_, fs)  => fs.values.flatMap(fromTerm).toSet
      case TMap(es)   => es.flatMap((k, v) => fromTerm(k) ++ fromTerm(v)).toSet
      case TTypeOf(t) => fromTerm(t)
      case _          => Set()
    f match
      case FNot(inner)   => outerAppNames(inner)
      case FEq(l, r)     => fromTerm(l) ++ fromTerm(r)
      case FLt(l, r)     => fromTerm(l) ++ fromTerm(r)
      case FExists(b, _) => fromTerm(b)

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
        .reverse
        .dropWhile(!w.contains(_))
        .reverse
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
            val nt =
              if (newTarget == "function(){}") s"class extends $name {}"
              else newTarget
            Some(
              s"Reflect.construct($name, [${args.mkString(", ")}], $nt)",
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
