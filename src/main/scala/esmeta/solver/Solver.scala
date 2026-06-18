package esmeta.solver

import esmeta.cfg.Func
import esmeta.spec.*
import esmeta.state.*
import esmeta.ty.*
import esmeta.util.BaseUtils.*

trait Solver { self: SymInterp =>

  import tychecker.*, SymTy.*

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
      code <- reify(
        path,
        thisV,
        vs,
        getNewTargetExpr(newTarget),
      )
    } yield code

  // get a JavaScript expression representing the may/must value type
  def getJSExpr(mayMustTy: (ValueTy, ValueTy)): Option[String] =
    val (mayTy, mustTy) = mayMustTy
    getJSExpr(mustTy).orElse(getJSExpr(mayTy))

  // get a JavaScript expression representing the value type
  def getJSExpr(ty: ValueTy): Option[String] =
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
    else Solver.defaultFor(ty)

  // get a JavaScript expression representing the newTarget value type
  def getNewTargetExpr(mayMustTy: (ValueTy, ValueTy)): Option[String] =
    val (mayTy, mustTy) = mayMustTy
    if (UndefT ⊑ mayTy) None else getJSExpr(mayTy)

  def getPath(func: Func): Option[BuiltinPath] = func.head match {
    case Some(h: BuiltinHead) => Some(h.path)
    case _                    => None
  }

  def reify(
    path: BuiltinPath,
    thisValue: String,
    args: List[String],
    newTarget: Option[String],
  ): Option[String] = newTarget match
    case Some(nt) =>
      Solver.access(path).map { target =>
        s"Reflect.construct($target, [${args.mkString(", ")}], $nt);"
      }
    case None =>
      path match
        case BuiltinPath.YetPath(_) => None
        case BuiltinPath.Getter(base) =>
          Solver.descriptor(base).map(d => s"$d.get.call($thisValue);")
        case BuiltinPath.Setter(base) =>
          val value = args.headOption.getOrElse("undefined")
          Solver.descriptor(base).map(d => s"$d.set.call($thisValue, $value);")
        case _ =>
          Solver.access(path).map { fn =>
            s"$fn.call(${(thisValue :: args).mkString(", ")});"
          }
}
object Solver {
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

  def defaultFor(ty: ValueTy): Option[String] =
    if (ty.isBottom) None
    else if (ty == ObjectT) Some("{}")
    else
      defaults
        .collectFirst { case (tyCase, js) if tyCase ⊑ ty => js }
        .orElse(defaults.collectFirst {
          case (tyCase, js) if !(ty && tyCase).isBottom => js
        })

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
