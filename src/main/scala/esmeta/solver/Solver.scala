package esmeta.solver

import esmeta.cfg.Func
import esmeta.fuzzer.mutator.Mutator
import esmeta.spec.*
import esmeta.state.*
import esmeta.ty.*
import esmeta.util.BaseUtils.*

trait Solver { self: SymInterp =>

  import tychecker.*, SymTy.*, Solver.*

  /** check the satisfiability of the given abstract state */
  def check: Boolean =
    val AbsState(reachable, locals, symEnv, constr) = st
    reachable &&
    symEnv.forall { case (sym, ty) => !ty.isBottom }

  /** reify a satisfiable path into an ECMAScript program */
  def reify: Option[String] =
    given AbsState = st
    val thisValue = st.getMayMust(SThis.sym)
    val rest = st.getMayMust(SArgs.sym) // TODO : handle variadic parameters
    val newTarget = st.getMayMust(SNewTarget.sym)
    val len = entryFunc.head match {
      case Some(h: BuiltinHead) => h.arity._2
      case _                    => 0
    }
    val args = (0 until len).toList.map(i => st.getMayMust(i))
    for {
      path <- getPath(entryFunc)
      thisV <- getJSExpr(thisValue)
      vs <- args.map(getJSExpr).sequence
      code <- buildJSProgram(path, thisV, vs, getNewTargetExpr(newTarget))
    } yield code

  /** reify a satisfiable path into candidate ECMAScript programs */
  def reifyCandidates(budget: Int = REIFY_BUDGET): List[String] =
    given AbsState = st
    val thisValue = st.getMayMust(SThis.sym)
    val rest = st.getMayMust(SArgs.sym) // TODO: handle variadic parameters
    val newTarget = st.getMayMust(SNewTarget.sym)
    val len = entryFunc.head match
      case Some(h: BuiltinHead) => h.arity._2
      case _                    => 0
    val args = (0 until len).toList.map(i => st.getMayMust(i))
    getPath(entryFunc)
      .map { path =>
        val thisCandidates = jsExprCandidates(thisValue, budget)
        val argCandidates = args.map(jsExprCandidates(_, budget))
        val ntCandidates = newTargetExprCandidates(newTarget, budget) match
          case Nil => List(None)
          case xs  => xs.map(Some(_))

        if (thisCandidates.isEmpty || argCandidates.exists(_.isEmpty)) Nil
        else {
          val baseThis = thisCandidates.head
          val baseArgs = argCandidates.map(_.head)
          val baseNt = ntCandidates.head
          def build(
            thisCode: String,
            argCodes: List[String],
            newTargetCode: Option[String],
          ): Option[String] =
            buildJSProgram(path, thisCode, argCodes, newTargetCode)
          // must type based candidate
          val base = build(baseThis, baseArgs, baseNt).toList
          // mutate only this value
          val thisMutants = thisCandidates.tail.flatMap { mut =>
            build(mut, baseArgs, baseNt)
          }
          // mutate only arguments
          val argMutants = argCandidates.zipWithIndex.flatMap { (exprs, idx) =>
            exprs.tail.flatMap { mut =>
              build(baseThis, baseArgs.updated(idx, mut), baseNt)
            }
          }
          // mutate only newTarget
          val ntMutants = ntCandidates.tail.flatMap { mut =>
            build(baseThis, baseArgs, mut)
          }
          (base ++ argMutants ++ thisMutants ++ ntMutants).distinct.take(budget)
        }
      }
      .getOrElse(Nil)
}
object Solver {

  val REIFY_BUDGET: Int = 8 // per-path budget for may-bounded fuzzing

  // get a JavaScript expression representing the may/must value type
  def getJSExpr(mayMustTy: (ValueTy, ValueTy)): Option[String] =
    val (mayTy, mustTy) = mayMustTy
    getJSExpr(mustTy).orElse(getJSExpr(mayTy))

  // get a JavaScript expression representing the value type
  def getJSExpr(ty: ValueTy): Option[String] = exprFor(ty)

  // get a JavaScript expression representing the newTarget value type
  def getNewTargetExpr(mayMustTy: (ValueTy, ValueTy)): Option[String] =
    val (mayTy, mustTy) = mayMustTy
    if (UndefT ⊑ mayTy) None else getJSExpr(mayTy)

  private def buildJSProgram(
    path: BuiltinPath,
    thisV: String,
    vs: List[String],
    newTarget: Option[String],
  ): Option[String] = newTarget match
    case Some(nt) =>
      access(path).map(target =>
        s"Reflect.construct($target, [${vs.mkString(", ")}], $nt);",
      )
    case None =>
      path match
        case BuiltinPath.YetPath(_) => None
        case BuiltinPath.Getter(base) =>
          descriptor(base).map(d => s"$d.get.call($thisV);")
        case BuiltinPath.Setter(base) =>
          val value = vs.headOption.getOrElse("undefined")
          descriptor(base).map(d => s"$d.set.call($thisV, $value);")
        case _ =>
          val args = (thisV :: vs).mkString(", ")
          access(path).map(fn => s"$fn.call($args);")

  private def jsExprCandidates(
    mayMustTy: (ValueTy, ValueTy),
    limit: Int = REIFY_BUDGET,
  ): List[String] =
    val (mayTy, mustTy) = mayMustTy
    val mustCandidates = jsExprCandidates(mustTy, limit)
    if (mustCandidates.nonEmpty) mustCandidates
    else jsExprCandidates(mayTy, limit)

  private def newTargetExprCandidates(
    mayMustTy: (ValueTy, ValueTy),
    limit: Int = REIFY_BUDGET,
  ): List[String] =
    val (mayTy, _) = mayMustTy
    if (UndefT ⊑ mayTy) Nil else jsExprCandidates(mayMustTy, limit)

  def getPath(func: Func): Option[BuiltinPath] = func.head match {
    case Some(h: BuiltinHead) => Some(h.path)
    case _                    => None
  }

  // JS expression to access a builtin function (None if unreachable)
  def funcAccessExpr(f: Func): Option[String] =
    f.head.collectFirst { case h: BuiltinHead => h.path }.flatMap(access)

  // JS expression accessing the builtin at path
  private def access(path: BuiltinPath): Option[String] = path match
    case BuiltinPath.Base(name) =>
      globalAlias.get(name) match
        case Some("")   => None // intrinsic unreachable from JS
        case Some(expr) => Some(expr)
        case None       => Some(name) // directly nameable global
    case BuiltinPath.NormalAccess(base, name) =>
      access(base).map(b => s"$b.$name")
    case BuiltinPath.SymbolAccess(base, sym) =>
      access(base).map(b => s"$b[Symbol.$sym]")
    case BuiltinPath.Getter(base) => access(base)
    case BuiltinPath.Setter(base) => access(base)
    case BuiltinPath.YetPath(_)   => None

  // Object.getOwnPropertyDescriptor(target, key) for a getter/setter base
  private def descriptor(base: BuiltinPath): Option[String] = base match
    case BuiltinPath.NormalAccess(b, n) =>
      val target = access(b)
      val key = s"\"${normStr(n)}\""
      target.map(t => s"Object.getOwnPropertyDescriptor($t, $key)")
    case BuiltinPath.SymbolAccess(b, s) =>
      val target = access(b)
      val key = s"Symbol.$s"
      target.map(t => s"Object.getOwnPropertyDescriptor($t, $key)")
    case _ => None

  // global alias for builtins that are not directly nameable but have a known JS expression to access them
  // https://github.com/tc39/test262/blob/main/harness/wellKnownIntrinsicObjects.js
  private val globalAlias: Map[String, String] = Map(
    "TypedArray" -> "Object.getPrototypeOf(Uint8Array)",
    "ArrayIteratorPrototype" -> "Object.getPrototypeOf([][Symbol.iterator]())",
    "AsyncFromSyncIteratorPrototype" -> "",
    "AsyncFunction" -> "(async function() {}).constructor",
    "AsyncGeneratorFunction" -> "(async function* () {}).constructor",
    "AsyncGeneratorPrototype" -> "Object.getPrototypeOf(async function* () {}).prototype",
    "AsyncIteratorPrototype" -> "Object.getPrototypeOf(Object.getPrototypeOf(async function* () {}).prototype)",
    "ForInIteratorPrototype" -> "",
    "GeneratorFunction" -> "(function* () {}).constructor",
    "GeneratorPrototype" -> "Object.getPrototypeOf(function * () {}).prototype",
    "IteratorHelperPrototype" -> "Object.getPrototypeOf(Iterator.from([]).drop(0))",
    "MapIteratorPrototype" -> "Object.getPrototypeOf(new Map()[Symbol.iterator]())",
    "SetIteratorPrototype" -> "Object.getPrototypeOf(new Set()[Symbol.iterator]())",
    "StringIteratorPrototype" -> "Object.getPrototypeOf(new String()[Symbol.iterator]())",
    "RegExpStringIteratorPrototype" -> """Object.getPrototypeOf(RegExp.prototype[Symbol.matchAll](""))""",
    "WrapForValidIteratorPrototype" -> "Object.getPrototypeOf(Iterator.from({ [Symbol.iterator](){ return {}; } }))",
    "ThrowTypeError" -> """(function() { "use strict"; return Object.getOwnPropertyDescriptor(arguments, "callee").get })()""",
  )

  def exprFor(ty: ValueTy): Option[String] =
    if (ty.number.contains(Number(0))) Some("0")
    else if (ty.number.contains(Number(-1))) Some("-1")
    else if (ty.number.contains(Number(1))) Some("1")
    else if (ty.number.contains(Number.NaN)) Some("NaN")
    else if (ty.number.contains(Number.Inf)) Some("Infinity")
    else if (ty.number.contains(-Number.Inf)) Some("-Infinity")
    else if (!ty.undef.isBottom) Some("undefined")
    else if (!ty.nullv.isBottom) Some("null")
    else if (ty.str.contains("")) Some("\"\"")
    else if (ty.bool.contains(false)) Some("false")
    else if (ty.bool.contains(true)) Some("true")
    else if (ty.bigInt.contains(BigInt(0))) Some("0n")
    else if (ty.bigInt.contains(BigInt(1))) Some("1n")
    else defaultFor(ty)

  def defaultFor(ty: ValueTy): Option[String] =
    if (ty.isBottom) None
    else
      objectWithProps(ty)
        .orElse(constructDescExpr(ty))
        .orElse(callDescExpr(ty))
        .orElse(baseDefaultFor(ty))

  private def constructDescExpr(ty: ValueTy): Option[String] =
    ty.record.construct match
      case ConstructDesc.Elem(exc, ret) =>
        if (exc) Some("function() { throw 0; }")
        else exprFor(ret).map(v => s"function() { return $v; }")
      case ConstructDesc.Top => None

  private def callDescExpr(ty: ValueTy): Option[String] =
    ty.record.call match
      case CallDesc.Elem(exc, ret) =>
        val isConstructor = ty <= ConstructorT
        if (exc)
          Some(
            if (isConstructor) "function() { throw 0; }"
            else "() => { throw 0; }",
          )
        else
          exprFor(ret).map { v =>
            if (isConstructor) s"function() { return $v; }"
            else s"() => ($v)"
          }
      case CallDesc.Top => None

  private def baseDefaultFor(ty: ValueTy): Option[String] =
    if (ty.isBottom) None
    else if (ty == ObjectT) Some("{}")
    else
      defaults
        .collectFirst { case (tyCase, js) if tyCase ⊑ ty => js }
        .orElse(defaults.collectFirst {
          case (tyCase, js) if ty overlap tyCase => js
        })

  private def isBasePlainObject(ty: ValueTy): Boolean = ty.record match
    case RecordTy.Elem(map, _) =>
      ObjectT ⊑ ty.copied(record = RecordTy.Elem(map))
    case _ => ObjectT ⊑ ty

  private def objectWithProps(ty: ValueTy): Option[String] =
    if (!isBasePlainObject(ty)) None
    else
      val props = properties(ty)
      if (props.nonEmpty && props.forall(_.isDefined))
        Some(props.flatten.mkString("{ ", ", ", " }"))
      else None

  private def properties(ty: ValueTy): List[Option[String]] =
    ty.record match
      case RecordTy.Elem(_, ObjShape(props, _, _)) =>
        // TODO call/construct descriptors
        props.toList.map { (prop, desc) =>
          val k = propKey(prop)
          if (desc.getExc) Some(s"get $k() { throw 0; }")
          else if (desc.setExc) Some(s"set $k(_) { throw 0; }")
          else if (!desc.ty.isBottom) exprFor(desc.ty).map(v => s"$k: $v")
          else None
        }
      case _ => Nil

  private def propKey(prop: Property): String = prop match
    case Property.PStr(str) => str
    case Property.PSym(sym) => s"[Symbol.$sym]"

  private def jsExprCandidates(ty: ValueTy, limit: Int): List[String] =
    if (limit <= 0 || ty.isBottom) Nil
    else
      objectExprCandidates(ty, limit).getOrElse {
        val base = exprFor(ty).toList
        val additions =
          if (ESValueT <= ty) // mutate if ESValueT
            Mutator.manualExprs.distinct.take(limit)
          else literalExprCandidates(ty)
        (base ++ additions).distinct.take(limit)
      }

  private def literalExprCandidates(ty: ValueTy): List[String] = List(
    if (!ty.undef.isBottom) Some("undefined") else None,
    if (!ty.nullv.isBottom) Some("null") else None,
    if (ty.str.contains("")) Some("\"\"") else None,
    if (ty.bool.contains(false)) Some("false") else None,
    if (ty.bool.contains(true)) Some("true") else None,
  ).flatten

  private def objectExprCandidates(
    ty: ValueTy,
    limit: Int,
  ): Option[List[String]] =
    if (!isBasePlainObject(ty)) None
    else {
      ty.record match
        case RecordTy.Elem(_, ObjShape(props, _, _)) if props.nonEmpty =>
          val propCandidates = propertyExprCandidates(props.toList, limit)
          if (propCandidates.forall(_.isDefined))
            Some(buildObjectExprs(propCandidates.flatten, limit))
          else Some(Nil)
        case _ => None
    }

  private def propertyExprCandidates(
    props: List[(Property, Desc)],
    limit: Int,
  ): List[Option[List[String]]] =
    // TODO: call/construct descriptors
    props.map { (prop, desc) =>
      val k = propKey(prop)
      if (desc.getExc) Some(List(s"get $k() { throw 0; }"))
      else if (desc.setExc) Some(List(s"set $k(_) { throw 0; }"))
      else if (!desc.ty.isBottom)
        Some(jsExprCandidates(desc.ty, limit).map(v => s"$k: $v").take(limit))
      else None
    }

  private def buildObjectExprs(
    props: List[List[String]],
    limit: Int,
  ): List[String] =
    if (props.exists(_.isEmpty)) Nil
    else
      val baseProps = props.map(_.head)
      val base = baseProps.mkString("{ ", ", ", " }")
      val mutants = props.zipWithIndex.flatMap { (candidates, idx) =>
        candidates.tail.map { candidate =>
          baseProps.updated(idx, candidate).mkString("{ ", ", ", " }")
        }
      }
      (base :: mutants).distinct.take(limit)

  private val defaults: List[(ValueTy, String)] = List(
    SymbolT -> "Symbol()",
    ConstructorT -> "function() {}",
    FunctionT -> "() => {}",
    RecordT("ProxyExoticObject") -> "new Proxy({}, {})",
    RecordT("BoundFunctionExoticObject") -> "(function(){}).bind()",
    RecordT("BuiltinFunctionObject") -> "Math.max",
    ArrayT -> "[]",
    TypedArrayT -> "new Int8Array()",
    RecordT("BigInt64Array") -> "new BigInt64Array()",
    RecordT("BigUint64Array") -> "new BigUint64Array()",
    RecordT("ArrayIteratorInstance") -> "[][Symbol.iterator]()",
    RegExpT -> "/./",
    RecordT("BooleanObject") -> "Object(true)",
    RecordT("NumberObject") -> "Object(0)",
    RecordT("StringExoticObject") -> "Object('')",
    RecordT("SymbolObject") -> "Object(Symbol())",
    RecordT("BigIntObject") -> "Object(0n)",
    RecordT("Map") -> "new Map()",
    RecordT("Set") -> "new Set()",
    RecordT("WeakMap") -> "new WeakMap()",
    RecordT("WeakSet") -> "new WeakSet()",
    RecordT("ArrayBuffer") -> "new ArrayBuffer(0)",
    RecordT("SharedArrayBuffer") -> "new SharedArrayBuffer(0)",
    RecordT("DataView") -> "new DataView(new ArrayBuffer(0))",
    RecordT("Date") -> "new Date()",
    RecordT("Promise") -> "new Promise(() => {})",
    RecordT("ErrorObject") -> "new Error()",
    RecordT("Generator") -> "(function*(){})()",
    RecordT("AsyncGenerator") -> "(async function*(){})()",
    RecordT("WeakRef") -> "new WeakRef({})",
    RecordT("FinalizationRegistry") -> "new FinalizationRegistry(() => {})",
    RecordT("ArgumentsExoticObject") -> "(function(){ return arguments; })()",
    ObjectT -> "{}",
  )
}
