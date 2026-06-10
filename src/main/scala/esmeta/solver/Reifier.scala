package esmeta.solver

import esmeta.cfg.Func
import esmeta.ir.*
import esmeta.spec.{BuiltinHead, BuiltinPath}
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.BaseUtils.normStr
import Formula.*, SymExpr.*

enum Access:
  case Slot(name: String)
  case Prop(key: String)
  case Method(name: String, key: Option[String] = None)

case class Model(
  ty: ValueTy = ESValueT,
  children: Map[Access, Model] = Map(),
  pin: Option[String] = None, // an exact literal JS witness (bypasses `ty`)
  // [Z3] FIXME: iterator NextMethod marker for hardcoded finiteness; see reifyIteratorNext
  iteratorNext: Boolean = false,
  excluded: Set[LiteralExpr] =
    Set(), // point exclusions (`!= 0`) the lattice cannot encode
  excludedTys: List[ValueTy] =
    Nil, // negated types whose subtraction over-prunes
  lower: Option[NumBound] = None, // numeric lower bound
  upper: Option[NumBound] = None, // numeric upper bound
)

// a numeric bound; `strict` excludes the bound value itself
case class NumBound(value: Double, strict: Boolean)

object Reifier {
  def apply(entry: Func, goal: List[Formula], syms: List[Sym]): Option[String] =
    witness(goal, syms).flatMap(assemble(entry, syms, _))

  // JS expression to access a builtin function (None if unreachable)
  def funcAccessExpr(f: Func): Option[String] =
    f.head.collectFirst { case h: BuiltinHead => h.path }.flatMap(access)

  private val default = "undefined" // fallback witness

  // per-sym witnesses; None if any sym cannot be reified (unsatisfiable shape)
  def witness(
    formulas: List[Formula],
    syms: List[Sym],
  ): Option[Map[Sym, String]] =
    val pairs = syms.map(sym => sym -> reifyValue(model(sym, formulas)))
    Option.when(pairs.forall(_._2.isDefined)) {
      pairs.collect { case (s, Some(js)) => s -> js }.toMap
    }

  /** model: fold a sym's goal formulas into its model */
  // TODO: NEEDS CODE REVIEW

  // narrow sym's Model by every goal formula
  def model(sym: Sym, formulas: List[Formula]): Model =
    formulas.foldLeft(Model())(refine(_, sym, _))

  // narrow sym's Model by one formula
  def refine(m: Model, sym: Sym, formula: Formula): Model =
    if (!formula.freeVars.contains(sym)) m
    else
      formula match
        // [Z3] FIXME: hardcoded iterator finiteness; remove when Z3 supplies the
        // result `done` constraint (then the call-return path reifies a finite
        // iterator on its own and this case can be deleted).
        case FTypeCheck(SERecord("IteratorRecord", fields), _) =>
          fields
            .get("NextMethod")
            .fold(m)(n => narrowAt(m, sym, n)(markIteratorNext))
        case FTypeCheck(t, ty)       => narrowAt(m, sym, t)(byTypeCheck(ty))
        case FEq(SELit(_), SELit(_)) => m
        // HasProperty(base, key) == bool: ordinary property presence/absence
        case FEq(
              ValueField(SECall("HasProperty", b :: rest)),
              SELit(EBool(exists)),
            ) =>
          hasProperty(m, sym, b, rest, exists)
        case FEq(
              SELit(EBool(exists)),
              ValueField(SECall("HasProperty", b :: rest)),
            ) =>
          hasProperty(m, sym, b, rest, exists)
        case FEq(SECall("HasProperty", b :: rest), SELit(EBool(exists))) =>
          hasProperty(m, sym, b, rest, exists)
        case FEq(SELit(EBool(exists)), SECall("HasProperty", b :: rest)) =>
          hasProperty(m, sym, b, rest, exists)
        case FEq(t, SELit(lit)) => narrowAt(m, sym, t)(byLiteral(lit))
        case FEq(SELit(lit), t) => narrowAt(m, sym, t)(byLiteral(lit))
        // value identical to a realm intrinsic: pin its JS access expression
        case FEq(t, intrinsicJs(js)) => narrowAt(m, sym, t)(pinTo(js))
        case FEq(intrinsicJs(js), t) => narrowAt(m, sym, t)(pinTo(js))
        case FExists(b, k @ SELit(EStr(_))) =>
          narrowAt(m, sym, SEField(b, k))(identity)
        case FNot(FExists(b, SELit(EStr(f)))) =>
          narrowAt(m, sym, b)(absentSlot(f))
        case FNot(FTypeCheck(t, ty)) => narrowAt(m, sym, t)(withoutTy(ty))
        case FNot(FEq(t, SELit(lit))) =>
          narrowAt(m, sym, t)(byExclusion(lit))
        case FNot(FEq(SELit(lit), t)) =>
          narrowAt(m, sym, t)(byExclusion(lit))
        case FLt(t, SELit(lit)) => narrowAt(m, sym, t)(boundAbove(lit, true))
        case FLt(SELit(lit), t) => narrowAt(m, sym, t)(boundBelow(lit, true))
        case FNot(FLt(t, SELit(lit))) =>
          narrowAt(m, sym, t)(boundBelow(lit, false))
        case FNot(FLt(SELit(lit), t)) =>
          narrowAt(m, sym, t)(boundAbove(lit, false))
        case _ => m

  // facts `refine` ignores for every sym -- the reifier never folds them into
  // any model, so the witness silently violates them; detected by reference
  // equality against the input model (stays in sync with `refine` by
  // construction), reported by the names of their outermost applications
  def droppedAppNames(fs: List[Formula], syms: List[Sym]): Set[String] =
    val init = Model()
    fs.iterator
      .filter(f => syms.forall(sym => refine(init, sym, f) eq init))
      .flatMap(Solver.outerAppNames)
      .toSet

  // narrowings: how one formula constrains the value at a position

  // the value is (also) of type `ty`
  private def meet(ty: ValueTy): Model => Model =
    m => m.copy(ty = m.ty && ty)

  // the value's exact JS witness is known (literal value / intrinsic identity)
  private def pinTo(js: String): Model => Model =
    m => m.copy(pin = Some(js))

  // the value equals a literal: pin its concrete JS witness directly (a Math
  // literal would otherwise meet ESValueT to bottom); a non-JS literal (enum,
  // code unit) has no JS form, so fall back to narrowing the type
  private def byLiteral(lit: LiteralExpr): Model => Model =
    litJs(lit) match
      case Some(js) => pinTo(js)
      case None     => meet(litTy(lit))

  // a literal directly as JS, without a round-trip through the type lattice
  // (whose canon folds -0 into the integer 0 and drops the sign)
  private def litJs(lit: LiteralExpr): Option[String] = lit match
    case ENumber(d)   => valueToJs(esmeta.state.Number(d))
    case EMath(n)     => valueToJs(esmeta.state.Math(n))
    case EBigInt(n)   => valueToJs(esmeta.state.BigInt(n))
    case EStr(s)      => valueToJs(esmeta.state.Str(s))
    case EBool(b)     => valueToJs(esmeta.state.Bool(b))
    case EUndef()     => Some("undefined")
    case ENull()      => Some("null")
    case EInfinity(p) => Some(if (p) "Infinity" else "-Infinity")
    case _            => None

  // the value is NOT of type `ty`; exact for whole types (the unsound point
  // exclusion is filtered out by `negTy`)
  private def without(ty: ValueTy): Model => Model =
    m => m.copy(ty = m.ty -- ty)

  // a ValueTy safe to subtract for `!= lit` (exact); None => ignore, since
  // point exclusion on a number/bigint/string over-prunes the lattice
  private def negTy(lit: LiteralExpr): Option[ValueTy] = lit match
    case _: EUndef | _: ENull | _: EBool | _: EEnum => Some(litTy(lit))
    case ENumber(d) if d.isNaN                      => Some(litTy(lit))
    case _                                          => None

  // the value differs from `lit`: subtract a whole type when exact, else
  // record a point exclusion for the sampler (the lattice cannot encode it)
  private def byExclusion(lit: LiteralExpr): Model => Model =
    negTy(lit) match
      case Some(nt) => withoutTy(nt)
      case None     => m => m.copy(excluded = m.excluded + lit)

  // the value is NOT of type `ty`, routed by how exact the subtraction is:
  // subtracting a partial number class collapses the sign lattice (e.g.
  // NumberT -- NumberIntT leaves only NaN), so keep the type and let the
  // sampler exclude candidates instead
  private def withoutTy(ty: ValueTy): Model => Model =
    if (ty.number.isBottom || ty.number.isTop) without(ty)
    else m => m.copy(excludedTys = m.excludedTys :+ ty)

  // the value is below `lit` (strictly if `strict`)
  private def boundAbove(lit: LiteralExpr, strict: Boolean): Model => Model =
    numericValue(lit) match
      case None => identity
      case Some(d) =>
        m => m.copy(upper = tighten(m.upper, NumBound(d, strict), true))

  // the value is above `lit` (strictly if `strict`); `!(t < lit)` is also
  // satisfied by NaN, but a `>= lit` witness satisfies it either way
  private def boundBelow(lit: LiteralExpr, strict: Boolean): Model => Model =
    numericValue(lit) match
      case None => identity
      case Some(d) =>
        m => m.copy(lower = tighten(m.lower, NumBound(d, strict), false))

  // keep the tighter of two bounds on one side
  private def tighten(
    cur: Option[NumBound],
    b: NumBound,
    upper: Boolean,
  ): Option[NumBound] =
    cur match
      case None => Some(b)
      case Some(c) =>
        if (b.value == c.value) Some(if (b.strict) b else c)
        else if (upper == (b.value < c.value)) Some(b)
        else Some(c)

  // a literal as a numeric bound value (NaN is unordered: no bound)
  private def numericValue(lit: LiteralExpr): Option[Double] = lit match
    case ENumber(d) if !d.isNaN => Some(d)
    case EMath(n)               => Some(n.toDouble)
    case EInfinity(p) =>
      Some(if (p) Double.PositiveInfinity else Double.NegativeInfinity)
    case _ => None

  // the value lacks internal slot `f`
  private def absentSlot(f: String): Model => Model =
    m =>
      m.copy(ty =
        m.ty.copied(record = m.ty.record.update(f, Binding.Absent, true)),
      )

  // [Z3] FIXME: mark an iterator's NextMethod for hardcoded finite reification
  private def markIteratorNext: Model => Model =
    m => m.copy(iteratorNext = true)

  // HasProperty(base, key) == bool: present -> add the ordinary property (an
  // own data property makes `key in base` true); absent -> a plain object lacks it
  private def hasProperty(
    m: Model,
    sym: Sym,
    base: SymExpr,
    rest: List[SymExpr],
    exists: Boolean,
  ): Model =
    // absence is satisfied by a default object; return a fresh copy so the
    // reference test in `droppedAppNames` counts the fact as consumed
    if (!exists) m.copy()
    else
      rest.find(k => propKey(k).isDefined).fold(m) { key =>
        narrowAt(m, sym, SECall("Get", List(base, key)))(identity)
      }

  // interpret a type-check `(? expr: ty)`: abrupt => the position throws
  // (ty<=AbruptT); normal completion => presence only; else => value meet
  private def byTypeCheck(ty: ValueTy): Model => Model =
    // abrupt REPLACES the value view: meeting would bottom out (a fresh child
    // is ESValueT and ESValueT && AbruptT = bottom), which withProps rejects
    // as unsatisfiable before its throwing-getter case can fire
    if (ty <= AbruptT) m => m.copy(ty = AbruptT)
    else if (ty <= CompT) identity
    else meet(ty)

  // locating: the access path from `sym` to what an expr names

  // the access path from `sym` to `expr`, or None if `expr` is not rooted at `sym`
  private def pathTo(sym: Sym, expr: SymExpr): Option[List[Access]] = expr match
    case SESym(s) => Option.when(s == sym)(Nil)
    case ValueField(c @ SECall(_, _)) =>
      pathTo(sym, c) // strip completion .Value
    case SECall("Get" | "GetV" | "GetMethod", args) =>
      getKey(args).flatMap((b, k) => pathTo(sym, b).map(_ :+ Access.Prop(k)))
    case SECall(name, b :: rest) if internalMethods(name) =>
      // keyed methods (Set/HasProperty/...): key = first arg resolving to a property key
      val method = Access.Method(name, rest.flatMap(propKey).headOption)
      pathTo(sym, b).map(_ :+ method)
    case StaticField(b, f) => pathTo(sym, b).map(_ :+ Access.Slot(f))
    case _                 => None

  // applying: narrow `m` at a located position

  // narrow `m` at `expr`'s position (relative to `sym`); no-op if not rooted at `sym`
  private def narrowAt(m: Model, sym: Sym, expr: SymExpr)(
    narrow: Model => Model,
  ): Model =
    pathTo(sym, expr).fold(m)(walk(m, _, narrow))

  // walk `path` from `m`, narrowing each container's kind, applying `narrow` at the leaf
  private def walk(
    m: Model,
    path: List[Access],
    narrow: Model => Model,
  ): Model =
    path match
      case Nil            => narrow(m)
      case access :: rest => descend(m, access, walk(_, rest, narrow))

  // one access step into `m`: narrow the container's kind, recurse into the child
  private def descend(m: Model, access: Access, narrow: Model => Model): Model =
    m.copy(
      ty = kindOf(m.ty, access),
      children = entry(m.children, access, narrow),
    )

  // narrow the container's ty for the access taken into it
  private def kindOf(ty: ValueTy, access: Access): ValueTy = access match
    case Access.Slot(f) =>
      ValueTy(record = ty.record.update(f, Binding.Exist, true))
    case _ => ty && ObjectT // prop/method => the container is an object

  // narrow one child entry (`top` if absent)
  private def entry(
    children: Map[Access, Model],
    access: Access,
    narrow: Model => Model,
  ): Map[Access, Model] =
    children.updated(access, narrow(children.getOrElse(access, Model())))

  // resolving keys and method names

  // Get(base, key) | Get(base, receiver, key) -> (base, key)
  private def getKey(args: List[SymExpr]): Option[(SymExpr, String)] =
    args match
      case b :: k :: Nil      => propKey(k).map(b -> _)
      case b :: _ :: k :: Nil => propKey(k).map(b -> _)
      case _                  => None

  // internal methods reached as a Method access (Get-family stays a Prop)
  private val internalMethods: Set[String] = Set(
    "Call",
    "Construct",
    "GetPrototypeOf",
    "SetPrototypeOf",
    "IsExtensible",
    "PreventExtensions",
    "OwnPropertyKeys",
    "Set",
    "HasProperty",
    "DefineOwnProperty",
    "Delete",
    "GetOwnProperty",
  )

  // the singleton ValueTy of a literal
  private def litTy(lit: LiteralExpr): ValueTy = lit match
    case EMath(n)     => MathT(n)
    case EInfinity(p) => InfinityT(p)
    case ENumber(n)   => NumberT(esmeta.state.Number(n))
    case EBigInt(_)   => BigIntT
    case EStr(s)      => StrT(s)
    case EBool(b)     => BoolT(b)
    case EUndef()     => UndefT
    case ENull()      => NullT
    case EEnum(name)  => EnumT(name)
    case ECodeUnit(_) => CodeUnitT

  // a property key as a String ("@@name" for well-known symbols), if literal
  private def propKey(e: SymExpr): Option[String] = e match
    case SELit(EStr(s))                            => Some(s)
    case SELit(EMath(n)) if n.isValidInt && n >= 0 => Some(n.toInt.toString)
    case SELit(ENumber(d)) if d >= 0 && d == d.toLong && !d.isInfinite =>
      Some(d.toLong.toString)
    case StaticField(SEGlobal("SYMBOL"), name) =>
      Some("@@" + name) // well-known symbol
    case _ => None

  // a realm intrinsic reference (`...Intrinsics["%Name%"]`) -> its JS access
  // expression; a dotted name is itself JS, an unnameable one maps via globalAlias
  private object intrinsicJs {
    def unapply(expr: SymExpr): Option[String] = expr match
      // realm-intrinsic lookup `<realm>.Intrinsics["%Name%"]` (the realm prefix
      // is a dynamic context reference, not reifiable; only the name matters)
      case StaticField(StaticField(_, "Intrinsics"), field)
          if field.startsWith("%") && field.endsWith("%") =>
        val inner = field.drop(1).dropRight(1)
        globalAlias.get(inner) match
          case Some("") => None // unreachable from JS
          case Some(js) => Some(js)
          case None     => Some(inner)
      case _ => None
  }

  /** reify: build a JS expression that witnesses a Model */
  // TODO: NEEDS CODE REVIEW

  // dispatch by what the Model is refined to
  def reifyValue(v: Model): Option[String] =
    if (v.pin.isDefined) v.pin // an exact literal value
    else if (v.ty.isBottom) None
    // [Z3] FIXME: `v.iteratorNext ||` routes hardcoded finite iterators here;
    // remove it (revert to the line below) once Z3 supplies `done` constraints.
    // else if (callReturn(v).isDefined || isConstructor(v) || v.ty <= FunctionT)
    else if (
      v.iteratorNext || callReturn(v).isDefined || isConstructor(
        v,
      ) || v.ty <= FunctionT
    )
      reifyFunction(v)
    else if (isObjectLike(v)) reifyObject(v)
    else reifyPrimitive(v)

  // a concrete literal: the pinned singleton value, else a sample honoring
  // point exclusions and bounds, else a default for `ty`
  def reifyPrimitive(v: Model): Option[String] =
    singleJs(v.ty).orElse(sample(v)).orElse(defaultFor(v.ty))

  // pick a witness honoring the point exclusions and numeric bounds that the
  // type lattice cannot encode (`!= 0`, `< 0`, not-an-integer, ...)
  private def sample(v: Model): Option[String] =
    val unconstrained = v.excluded.isEmpty && v.excludedTys.isEmpty &&
      v.lower.isEmpty && v.upper.isEmpty
    if (unconstrained) None
    else if (v.ty <= NumberT) sampleNumeric(v, true)
    else if (v.ty <= MathT) sampleNumeric(v, false)
    else if (v.ty <= BigIntT) sampleBigInt(v)
    else if (v.ty <= StrT) sampleStr(v)
    else None

  // literal membership in a type (the `<=` on a number singleton misses the
  // set-vs-int comparison, so numbers go through `contains`)
  private def inTy(lit: LiteralExpr, ty: ValueTy): Boolean = lit match
    case ENumber(d) => ty.number.contains(esmeta.state.Number(d))
    case EMath(n)   => ty.math.contains(esmeta.state.Math(n))
    case _          => litTy(lit) <= ty

  private def sampleNumeric(v: Model, number: Boolean): Option[String] =
    def toLit(d: Double): LiteralExpr =
      if (number) ENumber(d)
      else if (d.isInfinite) EInfinity(d > 0)
      else EMath(BigDecimal(d))
    def fits(d: Double): Boolean =
      val lit = toLit(d)
      inTy(lit, v.ty) &&
      !v.excludedTys.exists(inTy(lit, _)) &&
      !v.excluded.exists(sameLit(_, lit)) &&
      v.lower.forall(b => if (b.strict) d > b.value else d >= b.value) &&
      v.upper.forall(b => if (b.strict) d < b.value else d <= b.value)
    candidates(v.lower, v.upper).find(fits).flatMap(d => litJs(toLit(d)))

  // candidate ladder: simple integers, then bound-derived midpoints and
  // offsets (fractions reach non-integer-constrained positions), then infinities
  private def candidates(
    lower: Option[NumBound],
    upper: Option[NumBound],
  ): LazyList[Double] =
    val ints =
      LazyList(0.0, 1.0, -1.0, 2.0, -2.0, 3.0, -3.0, 10.0, -10.0, 100.0, -100.0)
    val lo = lower.map(_.value).filter(_.isFinite)
    val hi = upper.map(_.value).filter(_.isFinite)
    val mids = (lo, hi) match
      case (Some(a), Some(b)) =>
        val mid = (a + b) / 2
        LazyList(mid, (a + mid) / 2, (mid + b) / 2)
      case _ => LazyList.empty
    val nearLo =
      lo.fold(LazyList.empty[Double])(a => LazyList(a, a + 0.5, a + 1, a + 2))
    val nearHi =
      hi.fold(LazyList.empty[Double])(b => LazyList(b, b - 0.5, b - 1, b - 2))
    val infs = LazyList(Double.PositiveInfinity, Double.NegativeInfinity)
    ints ++ mids ++ nearLo ++ nearHi ++ infs

  // point-exclusion equality: distinguish +-0, identify NaN
  private def sameLit(a: LiteralExpr, b: LiteralExpr): Boolean = (a, b) match
    case (ENumber(x), ENumber(y)) => java.lang.Double.compare(x, y) == 0
    case _                        => a == b

  private def sampleBigInt(v: Model): Option[String] =
    LazyList(0, 1, -1, 2, -2, 3, -3, 10, -10, 100)
      .map(BigInt(_))
      .find(n => !v.excluded.exists(sameLit(_, EBigInt(n))))
      .map(n => s"${n}n")

  private def sampleStr(v: Model): Option[String] =
    LazyList("", "a", "b", "c", "x", "0", "1")
      .find { s =>
        litTy(EStr(s)) <= v.ty && !v.excluded.exists(sameLit(_, EStr(s)))
      }
      .map(s => "\"" + normStr(s) + "\"")

  // object from a creation form + ordinary __MAP__ (Prop) children; an internal
  // method constrained to throw makes it a Proxy with a throwing trap
  def reifyObject(v: Model): Option[String] =
    if (isRevokedProxy(v))
      Some(
        "(() => { const r = Proxy.revocable({}, {}); r.revoke(); return r.proxy; })()",
      )
    else
      throwingTraps(v) match
        case traps if traps.nonEmpty =>
          val body = traps.map(t => s"$t() { throw 0; }").mkString(", ")
          Some(s"new Proxy({}, { $body })")
        case _ => baseObject(v).flatMap(withProps(_, propChildren(v)))

  // a Proxy whose [[ProxyTarget]] is null is a revoked proxy
  private def isRevokedProxy(v: Model): Boolean =
    v.ty <= RecordT("ProxyExoticObject") &&
    v.children.get(Access.Slot("ProxyTarget")).exists(_.pin.contains("null"))

  // a callable: `() => return` (throwing if the call is abrupt); a constructor
  // becomes `function() {}` (arrows lack [[Construct]]), throwing if construct is abrupt
  def reifyFunction(v: Model): Option[String] =
    // [Z3] FIXME: hardcoded finite-iterator branch; remove once Z3 supplies the
    // result `done` constraint (the call-return path below then reifies a
    // terminating iterator), then delete reifyIteratorNext.
    if (v.iteratorNext) reifyIteratorNext(v)
    else
      val callRet = callReturn(v)
      val ctorRet = constructReturn(v)
      if (callRet.exists(_.ty <= AbruptT)) Some("() => { throw 0; }")
      else if (ctorRet.exists(_.ty <= AbruptT)) Some("function() { throw 0; }")
      else if (isConstructor(v))
        // [[Construct]] only honors an object return; emit it when constrained
        ctorRet.flatMap(reifyValue).filter(_ != default) match
          case Some(js) => Some(s"function() { return ($js); }")
          case None     => defaultFor(v.ty).orElse(Some("function() {}"))
      else
        callRet match
          case Some(ret) => reifyValue(ret).map(js => s"() => ($js)")
          // a specific function record (e.g. BuiltinFunctionObject) has its
          // own default witness; a generic arrow has [[SourceText]] and is
          // no witness for built-in-only constraints
          case None => defaultFor(v.ty).orElse(Some("() => {}"))

  // [Z3] FIXME: hardcoded finite iterator. The saturated formula only pins a
  // finite prefix of next() calls; termination of the unconstrained tail cannot
  // be derived, so we yield the constrained first result once then report done.
  // Once Z3 supplies the result `done` constraint, delete this and let the
  // regular call-return path reify a terminating iterator.
  def reifyIteratorNext(v: Model): Option[String] =
    val first = callReturn(v).flatMap(reifyValue).getOrElse("{}")
    Some(
      s"(() => { let i = 0; return () => (i++ ? { done: true } : $first); })()",
    )

  // creation form from the value's record type ([[Prototype]] / exotic / `{}`);
  // a non-object record (e.g. Symbol) is built from its own type, an ordinary
  // object from `ty && ObjectT`
  def baseObject(v: Model): Option[String] =
    (if (v.ty == ESValueT) None else defaultFor(v.ty))
      .orElse(defaultFor(v.ty && ObjectT))
      .orElse(Some("{}"))

  // attach ordinary props (abrupt -> throwing getter, else a data property)
  def withProps(base: String, props: Map[String, Model]): Option[String] =
    if (props.isEmpty) Some(base)
    else
      val rendered = props.toList.sortBy(_._1).map { (k, child) =>
        if (child.pin.isEmpty && child.ty.isBottom)
          None // unsatisfiable -> no witness
        else if (child.pin.isEmpty && child.ty <= AbruptT)
          Some(Left(k)) // the property read throws
        else reifyValue(child).map(js => Right(k -> js))
      }
      Option.when(rendered.forall(_.isDefined)) {
        val getters = rendered.flatten.collect { case Left(k) => k }
        val datas = rendered.flatten.collect { case Right(kv) => kv }
        if (base == "{}") {
          val body = (getters.map(k => s"get ${jsPropKey(k)}() { throw 0; }") ++
            datas.map((k, js) => s"${jsPropKey(k)}: $js")).mkString(", ")
          s"{ $body }"
        } else {
          // Object.assign would INVOKE a source getter at construction time,
          // so throwing getters are installed via Object.defineProperty
          val withData =
            if (datas.isEmpty) base
            else {
              val body =
                datas.map((k, js) => s"${jsPropKey(k)}: $js").mkString(", ")
              s"Object.assign($base, { $body })"
            }
          getters.foldLeft(withData) { (acc, k) =>
            s"Object.defineProperty($acc, ${definePropKey(k)}, " +
            "{ get: () => { throw 0; } })"
          }
        }
      }

  // a property key as a first-class JS expression (for defineProperty)
  private def definePropKey(key: String): String =
    if (key.startsWith("@@")) s"Symbol.${key.drop(2)}"
    else "\"" + normStr(key) + "\""

  // ----- reify helpers -----

  // the Model returned by calling `v`, if it has a Method("Call") child
  private def callReturn(v: Model): Option[Model] =
    v.children.collectFirst { case (Access.Method("Call", _), m) => m }

  // the Model produced by constructing `v`, if it has a Method("Construct") child
  private def constructReturn(v: Model): Option[Model] =
    v.children.collectFirst { case (Access.Method("Construct", _), m) => m }

  // `v` is constructible: a constructor type or a [[Construct]] slot/method
  private def isConstructor(v: Model): Boolean =
    v.ty <= ConstructorT || v.children.keysIterator.exists {
      case Access.Slot("Construct") | Access.Method("Construct", _) => true
      case _                                                        => false
    }

  // `v` looks like an object: object-typed or has structural children
  private def isObjectLike(v: Model): Boolean =
    v.ty <= ObjectT || v.children.keysIterator.exists {
      case _: Access.Slot | _: Access.Prop => true
      case _: Access.Method                => false
    }

  // ordinary __MAP__ (Prop) children of `v`
  private def propChildren(v: Model): Map[String, Model] =
    v.children.collect { case (Access.Prop(k), m) => k -> m }.toMap

  // proxy trap names for internal methods whose result is constrained abrupt
  private def throwingTraps(v: Model): List[String] =
    v.children.toList
      .collect {
        case (Access.Method(name, _), m)
            if m.ty <= AbruptT && proxyTraps.contains(name) =>
          proxyTraps(name)
      }
      .distinct
      .sorted

  // internal method -> Proxy trap (Call/Construct omitted: those reify as functions)
  private val proxyTraps: Map[String, String] = Map(
    "Get" -> "get",
    "Set" -> "set",
    "HasProperty" -> "has",
    "DefineOwnProperty" -> "defineProperty",
    "Delete" -> "deleteProperty",
    "GetOwnProperty" -> "getOwnPropertyDescriptor",
    "OwnPropertyKeys" -> "ownKeys",
    "GetPrototypeOf" -> "getPrototypeOf",
    "SetPrototypeOf" -> "setPrototypeOf",
    "IsExtensible" -> "isExtensible",
    "PreventExtensions" -> "preventExtensions",
  )

  // the pinned singleton value of `ty` as JS, if any
  private def singleJs(ty: ValueTy): Option[String] = ty.getSingle match
    case One(value) => valueToJs(value)
    case _          => None

  // a concrete ES value as JS
  private def valueToJs(value: esmeta.state.Value): Option[String] = value match
    case esmeta.state.Number(d) =>
      if (d.isNaN) Some("NaN")
      else if (d.isPosInfinity) Some("Infinity")
      else if (d.isNegInfinity) Some("-Infinity")
      else if (d == 0.0 && 1 / d < 0) Some("-0") // -0.0 == 0L hides the sign
      else if (d == d.toLong) Some(d.toLong.toString)
      else Some(d.toString)
    case esmeta.state.Math(n) =>
      Some(if (n.isWhole) n.toBigInt.toString else n.toString)
    case esmeta.state.BigInt(n)   => Some(s"${n}n")
    case esmeta.state.Str(s)      => Some("\"" + normStr(s) + "\"")
    case esmeta.state.Bool(b)     => Some(b.toString)
    case esmeta.state.Undef       => Some("undefined")
    case esmeta.state.Null        => Some("null")
    case esmeta.state.Infinity(p) => Some(if (p) "Infinity" else "-Infinity")
    case _                        => None

  // default JS witness for `ty` (specific records first, then primitives)
  private def defaultFor(ty: ValueTy): Option[String] =
    val found =
      if (ty.isBottom) None
      else if (ty == ESValueT)
        Some(default) // unconstrained -> safe (undefined)
      else if (ty == ObjectT)
        Some("{}") // generic object -> plain object literal
      else
        defaults
          .collectFirst { case (c, js) if ty <= c && c <= ty => js } // exact
          // a concrete default whose instances satisfy `ty` (e.g. a union like
          // ArrayBuffer|SharedArrayBuffer picks ArrayBuffer, not the ObjectT catch-all)
          .orElse(defaults.collectFirst { case (c, js) if c <= ty => js })
          .orElse(defaults.collectFirst {
            case (c, js) if ty <= c => js
          }) // subtype
          .orElse(defaults.collectFirst {
            case (c, js) if !(ty && c).isBottom => js
          })
    // function literals carry [[SourceText]]; when the type forbids the
    // slot, a bound function is the canonical callable without it
    found.map { js =>
      if (
        (js == "() => {}" || js == "function(){}") &&
        ty.record("SourceText").isAbsent
      ) "(function(){}).bind()"
      else js
    }

  private val defaults: List[(ValueTy, String)] = List(
    RecordT("TypedArray") -> "new Int8Array()",
    RecordT("ArrayIteratorInstance") -> "[][Symbol.iterator]()",
    RecordT("RegExp") -> "/./",
    RecordT("BuiltinFunctionObject") -> "Array.isArray",
    RecordT("BooleanObject") -> "Object(true)",
    RecordT("NumberObject") -> "Object(0)",
    RecordT("BigIntObject") -> "Object(0n)",
    RecordT("StringExoticObject") -> "Object('')",
    RecordT("Symbol") -> "Symbol()",
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
    RecordT("ProxyExoticObject") -> "new Proxy({}, {})",
    RecordT("BoundFunctionExoticObject") -> "(function(){}).bind()",
    RecordT("Array") -> "[]",
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

  // render an ordinary property key for an object literal
  private def jsPropKey(key: String): String =
    if (key.startsWith("@@")) s"[Symbol.${key.drop(2)}]"
    else if (isIdentifierName(key)) key
    else "\"" + normStr(key) + "\""

  private def isIdentifierName(s: String): Boolean =
    s.nonEmpty &&
    (s.head == '_' || s.head == '$' || s.head.isLetter) &&
    s.tail.forall(c => c == '_' || c == '$' || c.isLetterOrDigit)

  /** assembly: fill the template with witnesses */

  def assemble(
    entry: Func,
    syms: List[Sym],
    witness: Map[Sym, String],
  ): Option[String] =
    val entryPath = entry.head.collectFirst { case h: BuiltinHead => h.path }
    entryPath.flatMap { path =>
      val thisArg = witness(Sym.This)
      val newTarget = witness(Sym.NewTarget)
      val args = syms
        .collect { case arg: Sym.Arg => arg }
        .sortBy(_.index)
        .map(witness(_))
      if (newTarget != default) {
        access(path).map { target =>
          s"Reflect.construct($target, [${args.mkString(", ")}], $newTarget);"
        }
      } else {
        path match
          case BuiltinPath.YetPath(_) => None
          case BuiltinPath.Getter(base) =>
            Some(s"${descriptor(base)}.get.call($thisArg);")
          case BuiltinPath.Setter(base) =>
            val value = witness.getOrElse(Sym.Arg(0), default)
            Some(s"${descriptor(base)}.set.call($thisArg, $value);")
          case _ =>
            access(path).map(fn =>
              s"$fn.call(${(thisArg :: args).mkString(", ")});",
            )
      }
    }

  // Object.getOwnPropertyDescriptor(owner, key) for getter/setter base
  private def descriptor(base: BuiltinPath): String = base match
    case BuiltinPath.NormalAccess(owner, prop) =>
      s"Object.getOwnPropertyDescriptor(${access(owner).getOrElse("")}, ${"\"" + normStr(prop) + "\""})"
    case BuiltinPath.SymbolAccess(owner, sym) =>
      s"Object.getOwnPropertyDescriptor(${access(owner).getOrElse("")}, Symbol.$sym)"
    case _ => default

  // JS expression accessing the builtin at path
  private def access(path: BuiltinPath): Option[String] = path match
    case BuiltinPath.Base(name) =>
      globalAlias.get(name) match
        case Some("")   => None // intrinsic unreachable from JS
        case Some(expr) => Some(expr)
        case None       => Some(name) // directly nameable global
    case BuiltinPath.NormalAccess(base, name) =>
      Some(s"${access(base).getOrElse("")}.$name")
    case BuiltinPath.SymbolAccess(base, sym) =>
      Some(s"${access(base).getOrElse("")}[Symbol.$sym]")
    case BuiltinPath.Getter(base) => access(base)
    case BuiltinPath.Setter(base) => access(base)
    case BuiltinPath.YetPath(_)   => None

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
}
