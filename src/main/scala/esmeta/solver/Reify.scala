package esmeta.solver

import esmeta.cfg.Func
import esmeta.ir.*
import esmeta.spec.{BuiltinHead, BuiltinPath}
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.BaseUtils.*
import scala.collection.mutable.{Set => MSet}
import Formula.*, SymExpr.*

/** reify simplified formulas into JS code for entry parameters */
case class Reify(formulas: List[Formula], entryParams: List[Sym]) {
  import Reify.*

  def witness: Option[Witness] =
    if (hasUninterpretableApp(formulas)) None
    else {
      val normalized = formulas.map(normalizeEq)
      val omitted = normalized
        .collect {
          case FNot(FExists(SESym(Sym.ArgsList), SELit(EStr(idx)))) =>
            idx.toIntOption
        }
        .flatten
        .toSet
      val activeParams = entryParams.filterNot {
        case Sym.Arg(k) => omitted.contains(k)
        case _          => false
      }
      val pairs = activeParams.map { param =>
        val relevants = normalized.filter(_.freeVars.contains(param))
        buildExpr(param, relevants).map(param -> _)
      }
      if (pairs.forall(_.isDefined)) Some(pairs.flatten.toMap)
      else None
    }

  private def buildExpr(param: Sym, fs: List[Formula]): Option[String] =
    val consumed = MSet[Formula]()

    // literal equality
    val litVal = fs.collectFirst {
      case f @ FEq(SESym(_), SELit(lit)) => consumed += f; lit
    }

    // narrow type from type constraints and internal slot existence
    var ty = ESValueT
    for (f <- fs) f match
      case f @ FEq(SETypeOf(SESym(_)), SEType(pos)) =>
        consumed += f; ty = ty && pos
      case f @ FNot(FEq(SETypeOf(SESym(_)), SEType(neg))) =>
        consumed += f; ty = ty -- neg
      case f @ FExists(SESym(_), SELit(EStr(field)))
          if fieldToRecordTy.contains(field) =>
        consumed += f; ty = ty && fieldToRecordTy(field)
      case f @ FNot(FExists(SESym(_), SELit(EStr(field))))
          if fieldToRecordTy.contains(field) =>
        consumed += f; ty = ty -- fieldToRecordTy(field)
      case _ => ()
    val narrowedTy = ty
    val hasTyConstraint = narrowedTy != ESValueT

    // typed/abrupt property constraints — only when the base is an object
    // literal that can have properties merged into it
    val objLiteralBase = defaultFor(narrowedTy).exists(_.startsWith("{"))

    // property constraints from Get/HasProperty
    val propsValue = fs.collect {
      case f @ FEq(SEApp("Get", List(_, SELit(EStr(key)))), SELit(lit)) =>
        consumed += f; (key, lit)
    }.toMap
    val propsAbrupt =
      if (objLiteralBase) fs.collect {
        case f @ FEq(
              SETypeOf(SEApp("Get", List(_, SELit(EStr(key))))),
              SEType(ty),
            ) if ty <= AbruptT =>
          consumed += f; key
      }.toSet
      else Set.empty[String]
    val propsExist = fs.collect {
      case f @ FEq(
            SEApp("HasProperty", List(_, SELit(EStr(key)))),
            SELit(EBool(exists)),
          ) =>
        consumed += f; (key, exists)
      case f @ FExists(SESym(_), SELit(EStr(field)))
          if !fieldToRecordTy.contains(field) =>
        consumed += f; (field, true)
      case f @ FNot(FExists(SESym(_), SELit(EStr(field))))
          if !fieldToRecordTy.contains(field) =>
        consumed += f; (field, false)
    }.toMap
    val propsTyped =
      if (objLiteralBase) fs.collect {
        case f @ FEq(
              SETypeOf(SEApp("Get", List(_, SELit(EStr(key))))),
              SEType(ty),
            ) if !(ty <= AbruptT) && !(ty <= NormalT) =>
          consumed += f; (key, ty)
      }.toMap
      else Map.empty[String, ValueTy]
    if (objLiteralBase) for (f <- fs) f match
      case f @ FNot(FEq(SEApp("Get", List(_, SELit(EStr(_)))), SELit(_))) =>
        consumed += f
      case f @ FNot(
            FEq(SETypeOf(SEApp("Get", List(_, SELit(EStr(_))))), SEType(_)),
          ) =>
        consumed += f
      case _ => ()

    // object config from IsExtensible/GetPrototypeOf
    val extensible = fs.collectFirst {
      case f @ FEq(SEApp("IsExtensible", _), SELit(EBool(false))) =>
        consumed += f; false
      case f @ FEq(SEApp("IsExtensible", _), SELit(EBool(true))) =>
        consumed += f; true
    }
    val prototype = fs.collectFirst {
      case f @ FEq(SEApp("GetPrototypeOf", _), SELit(lit)) =>
        consumed += f; lit
    }

    // disequality constraints
    val excluded = fs.collect {
      case f @ FNot(FEq(SESym(_), SELit(lit))) => consumed += f; lit
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
      case f @ FLt(SESym(_), SELit(lit)) => // x < k
        numVal(lit).foreach(k => {
          consumed += f; hiStrict = Some(hiStrict.fold(k)(_ min k))
        })
      case f @ FLt(SELit(lit), SESym(_)) => // k < x
        numVal(lit).foreach(k => {
          consumed += f; loStrict = Some(loStrict.fold(k)(_ max k))
        })
      case f @ FNot(FLt(SESym(_), SELit(lit))) => // x >= k
        numVal(lit).foreach(k => {
          consumed += f; loIncl = Some(loIncl.fold(k)(_ max k))
        })
      case f @ FNot(FLt(SELit(lit), SESym(_))) => // k >= x
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
    else if (unconsumed.nonEmpty)
      val extraTraps = List.newBuilder[Formula]
      val p = SESym(param)
      extensible.foreach(b =>
        extraTraps += FEq(SEApp("IsExtensible", List(p)), SELit(EBool(b))),
      )
      prototype.foreach(lit =>
        extraTraps += FEq(SEApp("GetPrototypeOf", List(p)), SELit(lit)),
      )
      buildProxy(narrowedTy, unconsumed ++ extraTraps.result())
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
      case (Some(false), Some(ENull())) =>
        s"Object.preventExtensions(Object.create(null))"
      case (Some(false), _)   => s"Object.preventExtensions($objLiteral)"
      case (_, Some(ENull())) => "Object.create(null)"
      case _                  => objLiteral
  }

  // build Proxy from unhandled trap formulas
  private def buildProxy(
    ty: ValueTy,
    trapFormulas: List[Formula],
  ): Option[String] =
    val rawTarget = trapFormulas
      .collectFirst {
        case FEq(SETypeOf(SEApp(fname: String, _)), SEType(_)) =>
          proxyTarget(fname)
        case FEq(SEApp(fname: String, _), _)       => proxyTarget(fname)
        case FNot(FEq(SEApp(fname: String, _), _)) => proxyTarget(fname)
        case FNot(FEq(SETypeOf(SEApp(fname: String, _)), SEType(_))) =>
          proxyTarget(fname)
      }
      .getOrElse("{}")
    val target =
      if (rawTarget == "{}" && ty <= ConstructorT) "function(){}"
      else if (rawTarget == "{}" && ty <= FunctionT) "() => {}"
      else rawTarget

    val traps = List.newBuilder[(String, String)]
    for (formula <- trapFormulas) formula match
      case FEq(SETypeOf(SEApp(fname: String, _)), SEType(ty))
          if ty <= AbruptT =>
        proxyTrapName.get(fname).foreach(trap => traps += trap -> "throw 0;")
      case FEq(SEApp(fname: String, _), SELit(lit)) =>
        for {
          jsLit <- litToJs(lit)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsLit;"
      case FNot(FEq(SEApp(fname: String, _), SELit(lit))) =>
        for {
          jsVal <- defaultFor(ESValueT, Set(lit))
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case FEq(SETypeOf(SEApp(fname: String, _)), SEType(ty))
          if !(ty <= AbruptT) && !(ty <= NormalT) =>
        for {
          jsVal <- defaultFor(ty)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case FNot(FEq(SETypeOf(SEApp(fname: String, _)), SEType(ty)))
          if !(ty <= AbruptT) && !(ty <= NormalT) =>
        for {
          jsVal <- defaultFor(ESValueT -- ty)
          trap <- proxyTrapName.get(fname)
        } traps += trap -> s"return $jsVal;"
      case _ => ()

    val trapList = traps.result()
    if (trapList.isEmpty) return None

    val needsNonExtensible = trapList.exists { (name, body) =>
      name == "preventExtensions" ||
      (name == "isExtensible" && body != "return true;")
    }
    val finalTarget =
      if (needsNonExtensible) s"Object.preventExtensions($target)"
      else target
    val trapStr =
      trapList.map((name, body) => s"$name() { $body }").mkString(", ")
    Some(s"new Proxy($finalTarget, { $trapStr })")
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
    case EStr(s) =>
      val escaped = s
        .replace("\\", "\\\\")
        .replace("\"", "\\\"")
        .replace("\n", "\\n")
        .replace("\r", "\\r")
        .replace("\t", "\\t")
      Some(s"\"$escaped\"")
    case EMath(n) =>
      Some(if (n.isWhole) n.toBigInt.toString else n.toString)
    case ENumber(d) =>
      if (d.isNaN) Some("NaN")
      else if (d.isPosInfinity) Some("Infinity")
      else if (d.isNegInfinity) Some("-Infinity")
      else if (isNegZero(d)) Some("-0")
      else if (d == d.toLong && !d.isInfinite) Some(d.toLong.toString)
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
    RecordT("ProxyExoticObject") -> "new Proxy({}, {})",
    RecordT("BoundFunctionExoticObject") -> "(function(){}).bind()",
    RecordT("Array") -> "[]",
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
      .orElse {
        // 5. fallback for excluded primitive defaults
        if (ty <= NumberT)
          List("1", "-1", "0.5", "2", "100").find(!excJs(_))
        else if (ty <= StrT)
          List("\"a\"", "\"test\"").find(!excJs(_))
        else None
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
    case FEq(l: SELit, r) if !r.isInstanceOf[SELit]       => FEq(r, l)
    case FNot(FEq(l: SELit, r)) if !r.isInstanceOf[SELit] => FNot(FEq(r, l))
    case _                                                => f

  def hasUninterpretableApp(fs: List[Formula]): Boolean =
    def fromExpr(t: SymExpr): Set[String] = t match
      case SEApp(fname: String, args) => Set(fname) ++ args.flatMap(fromExpr)
      case SEApp(_, args)             => args.flatMap(fromExpr).toSet
      case SEProj(base, _)            => fromExpr(base)
      case SEList(elems)              => elems.flatMap(fromExpr).toSet
      case SERecord(_, fs)            => fs.values.flatMap(fromExpr).toSet
      case SEMap(es) =>
        es.flatMap((k, v) => fromExpr(k) ++ fromExpr(v)).toSet
      case SETypeOf(t) => fromExpr(t)
      case _           => Set()
    def fromFormula(f: Formula): Set[String] = f match
      case FNot(inner)   => fromFormula(inner)
      case FEq(l, r)     => fromExpr(l) ++ fromExpr(r)
      case FLt(l, r)     => fromExpr(l) ++ fromExpr(r)
      case FExists(b, _) => fromExpr(b)
    fs.exists(fromFormula(_).exists(!internalMethods.contains(_)))

  def outerAppNames(f: Formula): Set[String] =
    def fromExpr(t: SymExpr): Set[String] = t match
      case SEApp(fname: String, _) if !internalMethods(fname) => Set(fname)
      case SEApp(_, args)  => args.flatMap(fromExpr).toSet
      case SEProj(base, _) => fromExpr(base)
      case SEList(elems)   => elems.flatMap(fromExpr).toSet
      case SERecord(_, fs) => fs.values.flatMap(fromExpr).toSet
      case SEMap(es) =>
        es.flatMap((k, v) => fromExpr(k) ++ fromExpr(v)).toSet
      case SETypeOf(t) => fromExpr(t)
      case _           => Set()
    f match
      case FNot(inner)   => outerAppNames(inner)
      case FEq(l, r)     => fromExpr(l) ++ fromExpr(r)
      case FLt(l, r)     => fromExpr(l) ++ fromExpr(r)
      case FExists(b, _) => fromExpr(b)

  /** JS expression to access a builtin function */
  def funcAccessExpr(f: Func): Option[String] =
    f.head
      .collect { case h: BuiltinHead => h.path }
      .map(pathStr)
      .filter(_.nonEmpty)

  /** build a JS call that invokes the builtin with solved arguments */
  def toJsCall(func: Func, params: List[Sym], w: Witness): Option[String] =
    func.head.collect { case h: BuiltinHead => h }.flatMap { h =>
      val thisVal = w.getOrElse(Sym.This, "undefined")
      val newTarget = w.getOrElse(Sym.NewTarget, "undefined")
      val argIds = params
        .collect { case id @ Sym.Arg(_) => id }
        .sortBy(_.index)
      val args = argIds.reverse
        .dropWhile(id => !w.contains(id))
        .reverse
        .map(id => w.getOrElse(id, "undefined"))
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
              else if (newTarget.startsWith("new Proxy({},"))
                newTarget.replaceFirst(
                  raw"new Proxy\(\{},",
                  "new Proxy(function(){},",
                )
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
