package esmeta.solver

import esmeta.cfg.Func
import esmeta.ir.*
import esmeta.spec.{BuiltinHead, BuiltinPath}
import esmeta.ty.*
import esmeta.util.*
import esmeta.util.BaseUtils.*
import Formula.*, SymExpr.*

/** reify simplified formulas into JS code for entry parameters */
case class Reify(
  formulas: List[Formula],
  entryParams: List[Sym],
) {
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
      collectFacts(normalized.filterNot(isOmittedArgFormula)).flatMap {
        factMap =>
          val pairs = activeParams.map { param =>
            renderParam(param, factMap).map(param -> _)
          }
          if (pairs.forall(_.isDefined)) Some(pairs.flatten.toMap)
          else None
      }
    }

  private def isOmittedArgFormula(f: Formula): Boolean = f match
    case FNot(FExists(SESym(Sym.ArgsList), SELit(EStr(idx)))) =>
      idx.toIntOption.isDefined
    case _ => false
}

object Reify {
  enum Fact:
    case Type(ty: ValueTy)
    case NotType(ty: ValueTy)
    case Value(lit: LiteralExpr)
    case NotValue(lit: LiteralExpr)
    case Lower(lit: LiteralExpr, strict: Boolean)
    case Upper(lit: LiteralExpr, strict: Boolean)
    case Prop(key: String, fact: Fact)
    case PropExists(key: String, exists: Boolean)
    case Call(fact: Fact)
    case Extensible(value: Boolean)
    case Prototype(lit: LiteralExpr)
    case Trap(name: String, fact: Fact)
    case Field(name: String, fact: Fact)
    case FieldExists(name: String, exists: Boolean)

  type FactMap = Map[Sym, Set[Fact]]

  private def collectFacts(formulas: List[Formula]): Option[FactMap] =
    val entries = formulas.map(factsOf)
    if (entries.forall(_.isDefined))
      Some(
        entries.flatten.flatten
          .groupMap(_._1)(_._2)
          .view
          .mapValues(_.toSet)
          .toMap,
      )
    else None

  private def factsOf(formula: Formula): Option[List[(Sym, Fact)]] =
    formula match
      case FTypeCheck(term, ty) =>
        typeFacts(term, ty, positive = true)
      case FNot(FTypeCheck(term, ty)) =>
        typeFacts(term, ty, positive = false)
      case FEq(term, SELit(lit)) =>
        valueFacts(term, lit, positive = true)
      case FNot(FEq(term, SELit(lit))) =>
        valueFacts(term, lit, positive = false)
      case FExists(base, SELit(EStr(field))) =>
        existsFacts(base, field, exists = true)
      case FNot(FExists(base, SELit(EStr(field)))) =>
        existsFacts(base, field, exists = false)
      case FLt(term, SELit(lit)) =>
        termFact(term, Fact.Upper(lit, strict = true))
      case FLt(SELit(lit), term) =>
        termFact(term, Fact.Lower(lit, strict = true))
      case FNot(FLt(term, SELit(lit))) =>
        termFact(term, Fact.Lower(lit, strict = false))
      case FNot(FLt(SELit(lit), term)) =>
        termFact(term, Fact.Upper(lit, strict = false))
      case _ => None

  private def valueFacts(
    term: SymExpr,
    lit: LiteralExpr,
    positive: Boolean,
  ): Option[List[(Sym, Fact)]] =
    term match
      case SEApp("HasProperty", List(base, key)) =>
        lit match
          case EBool(exists) =>
            hasPropertyFact(
              base,
              key,
              Fact.Value(EBool(if (positive) exists else !exists)),
            )
          case _ => None
      case SEApp("HasProperty", base :: _ :: key :: Nil) =>
        lit match
          case EBool(exists) =>
            hasPropertyFact(
              base,
              key,
              Fact.Value(EBool(if (positive) exists else !exists)),
            )
          case _ => None
      case SEApp("IsExtensible", base :: _) =>
        lit match
          case EBool(value) =>
            termFact(
              base,
              Fact.Extensible(if (positive) value else !value),
            )
          case _ => None
      case SEApp("GetPrototypeOf", base :: _) if positive =>
        termFact(base, Fact.Prototype(lit))
      case SEApp(fname: String, base :: _) if isTrapOnlyMethod(fname) =>
        termFact(
          base,
          Fact.Trap(
            fname,
            if (positive) Fact.Value(lit) else Fact.NotValue(lit),
          ),
        )
      case _ =>
        termFact(
          term,
          if (positive) Fact.Value(lit) else Fact.NotValue(lit),
        )

  private def typeFacts(
    term: SymExpr,
    ty: ValueTy,
    positive: Boolean,
  ): Option[List[(Sym, Fact)]] =
    val fact = if (positive) Fact.Type(ty) else Fact.NotType(ty)
    term match
      case SEApp("HasProperty", List(base, key)) =>
        if (isDefaultNormal(ty, positive))
          termFact(base, Fact.Type(ObjectT))
        else hasPropertyFact(base, key, fact)
      case SEApp("HasProperty", base :: _ :: key :: Nil) =>
        if (isDefaultNormal(ty, positive))
          termFact(base, Fact.Type(ObjectT))
        else hasPropertyFact(base, key, fact)
      case SEApp(fname: String, base :: _)
          if fname == "IsExtensible" || fname == "GetPrototypeOf" =>
        if (isDefaultNormal(ty, positive))
          termFact(base, Fact.Type(ObjectT))
        else termFact(base, Fact.Trap(fname, fact))
      case SEApp(fname: String, base :: _) if isTrapOnlyMethod(fname) =>
        if (isDefaultNormal(ty, positive))
          termFact(base, Fact.Type(ObjectT))
        else termFact(base, Fact.Trap(fname, fact))
      case _ => termFact(term, fact)

  private def existsFacts(
    base: SymExpr,
    field: String,
    exists: Boolean,
  ): Option[List[(Sym, Fact)]] =
    val fact = fieldToRecordTy.get(field) match
      case Some(ty) => if (exists) Fact.Type(ty) else Fact.NotType(ty)
      case None     => Fact.FieldExists(field, exists)
    termFact(base, fact)

  private def termFact(
    term: SymExpr,
    fact: Fact,
  ): Option[List[(Sym, Fact)]] = term match
    case SESym(sym) =>
      Some(List(sym -> fact))
    case ValueField(SEApp("Get", List(base, key))) =>
      getFact(base, key, fact)
    case ValueField(SEApp("Get", base :: _ :: key :: _)) =>
      getFact(base, key, fact)
    case ValueField(SEApp("GetV", List(base, key))) =>
      getFact(base, key, fact)
    case ValueField(SEApp("GetMethod", List(base, key))) =>
      getFact(base, key, fact)
    case ValueField(SEApp("HasProperty", List(base, key))) =>
      hasPropertyFact(base, key, fact)
    case ValueField(SEApp("HasProperty", base :: _ :: key :: Nil)) =>
      hasPropertyFact(base, key, fact)
    case ValueField(SEApp("Call", fn :: _)) =>
      termFact(fn, Fact.Call(fact))
    case ValueField(SEApp("Construct", ctor :: _)) =>
      termFact(ctor, Fact.Trap("Construct", fact))
    case ValueField(SEApp("GetPrototypeOf", base :: _)) =>
      fact match
        case Fact.Value(lit) => termFact(base, Fact.Prototype(lit))
        case _ => termFact(base, Fact.Trap("GetPrototypeOf", fact))
    case ValueField(SEApp("IsExtensible", base :: _)) =>
      fact match
        case Fact.Value(EBool(value)) =>
          termFact(base, Fact.Extensible(value))
        case Fact.NotValue(EBool(value)) =>
          termFact(base, Fact.Extensible(!value))
        case _ => termFact(base, Fact.Trap("IsExtensible", fact))
    case ValueField(SEApp(fname: String, base :: _))
        if isTrapOnlyMethod(fname) =>
      termFact(base, Fact.Trap(fname, fact))
    case SEApp("Get", List(base, key)) =>
      getFact(base, key, fact)
    case SEApp("Get", base :: _ :: key :: _) =>
      getFact(base, key, fact)
    case SEApp("Call", fn :: _) =>
      termFact(fn, Fact.Call(fact))
    case SEApp("Construct", ctor :: _) =>
      termFact(ctor, Fact.Trap("Construct", fact))
    case SEApp(fname: String, base :: _) if isTrapOnlyMethod(fname) =>
      termFact(base, Fact.Trap(fname, fact))
    case SEField(base, field) =>
      termFact(base, Fact.Field(field, fact))
    case _ => None

  private def getFact(
    base: SymExpr,
    key: SymExpr,
    fact: Fact,
  ): Option[List[(Sym, Fact)]] =
    propKey(key) match
      case Some(k) => termFact(base, Fact.Prop(k, fact))
      case None    => termFact(base, Fact.Trap("Get", fact))

  private def hasPropertyFact(
    base: SymExpr,
    key: SymExpr,
    fact: Fact,
  ): Option[List[(Sym, Fact)]] =
    propKey(key) match
      case Some(k) if fact == Fact.Value(EBool(true)) =>
        termFact(base, Fact.PropExists(k, exists = true))
      case Some(k) =>
        termFact(
          base,
          Fact.Trap("HasProperty", Fact.Prop(k, fact)),
        )
      case None =>
        termFact(base, Fact.Trap("HasProperty", fact))

  private def isTrapOnlyMethod(name: String): Boolean =
    isInternalMethod(name) &&
    name != "Get" &&
    name != "Call" &&
    name != "Construct" &&
    name != "HasProperty" &&
    name != "IsExtensible" &&
    name != "GetPrototypeOf"

  private def isDefaultNormal(ty: ValueTy, positive: Boolean): Boolean =
    (positive && ty <= NormalT) || (!positive && ty <= AbruptT)

  private def renderParam(param: Sym, factMap: FactMap): Option[String] =
    val facts = factMap.getOrElse(param, Set.empty)
    param match
      case Sym.NewTarget => renderNewTarget(facts)
      case _ =>
        if (facts.isEmpty) Some("undefined")
        else if (isDirectAbruptCompletion(facts)) Some(abruptConversionObject)
        else renderFacts(facts)

  private def renderNewTarget(facts: Set[Fact]): Option[String] =
    if (facts.isEmpty) Some("undefined")
    else
      val parts = partitionFacts(facts)
      val hasInvalidValue = parts.values.exists(lit => !isUndefinedLiteral(lit))
      if (hasInvalidValue || parts.values.size > 1 || hasNumericBounds(parts))
        None
      else
        val requiresConstructor = newTargetRequiresConstructor(parts)
        if (!requiresConstructor && newTargetAllowsUndefined(parts))
          Some("undefined")
        else renderConstructorTarget(parts)

  private def newTargetAllowsUndefined(parts: FactParts): Boolean =
    val requiredTy = requiredValueType(parts)
    parts.values.forall(isUndefinedLiteral) &&
    !parts.excluded.exists(isUndefinedLiteral) &&
    !hasObjectShape(parts) &&
    parts.calls.isEmpty &&
    parts.traps.isEmpty &&
    !(requiredTy && UndefT).isBottom &&
    !parts.avoidedTypes.exists(ty => overlaps(ty, UndefT))

  private def newTargetRequiresConstructor(parts: FactParts): Boolean =
    parts.excluded.exists(isUndefinedLiteral) ||
    parts.avoidedTypes.exists(ty => overlaps(ty, UndefT)) ||
    hasObjectShape(parts) ||
    parts.calls.nonEmpty ||
    parts.traps.nonEmpty ||
    parts.types.exists(ty =>
      ty <= ObjectT || ty <= FunctionT || ty <= ConstructorT,
    )

  private def renderConstructorTarget(parts: FactParts): Option[String] =
    val requiredTy = requiredValueType(parts)
    val avoidedTys = avoidedValueTypes(parts)
    if (parts.values.nonEmpty) None
    else if ((requiredTy && ConstructorT).isBottom) None
    else if (avoidedTys.exists(ty => overlaps(ty, ConstructorT))) None
    else
      for {
        prepared <- prepareConstructorPrototype(parts)
        (base, objectParts, extraTraps) = prepared
        configured <- renderObjectLike(base, objectParts)
        trapped <- renderTraps(
          configured,
          mergeTraps(objectParts.traps, extraTraps),
        )
      } yield trapped

  private def prepareConstructorPrototype(
    parts: FactParts,
  ): Option[(String, FactParts, Map[String, Set[Fact]])] =
    val prototypeProps = parts.props.getOrElse("prototype", Set.empty)
    val prototypeHas = parts.propExists.get("prototype")
    if (prototypeHas.exists(_.size > 1)) None
    else
      val prototypeGet =
        if (prototypeProps.nonEmpty)
          renderTrapFacts(prototypeProps)
        else Some(None)
      prototypeGet.flatMap { getBody =>
        val hasFalse = prototypeHas.exists(_.contains(false))
        val hasTrue = prototypeHas.exists(_.contains(true))
        val needsBoundTarget = getBody.isDefined || hasFalse
        renderConstructorFunction(parts.calls).map { rawBase =>
          val base =
            if (needsBoundTarget) bindConstructor(rawBase)
            else rawBase
          val objectParts = parts.copy(
            props = parts.props - "prototype",
            propExists = parts.propExists - "prototype",
          )
          val getTrap =
            if (getBody.isDefined)
              Map("Get" -> prototypeProps.map(Fact.Prop("prototype", _)))
            else Map.empty[String, Set[Fact]]
          val hasTrap =
            if (hasTrue && needsBoundTarget)
              Map(
                "HasProperty" ->
                Set(Fact.Prop("prototype", Fact.Value(EBool(true)))),
              )
            else Map.empty[String, Set[Fact]]
          (base, objectParts, mergeTraps(getTrap, hasTrap))
        }
      }

  private def bindConstructor(base: String): String =
    s"($base).bind(null)"

  private def mergeTraps(
    left: Map[String, Set[Fact]],
    right: Map[String, Set[Fact]],
  ): Map[String, Set[Fact]] =
    (left.keySet ++ right.keySet)
      .map(key =>
        key -> (left.getOrElse(key, Set.empty) ++ right
          .getOrElse(key, Set.empty)),
      )
      .toMap

  private def renderConstructorFunction(callFacts: Set[Fact]): Option[String] =
    if (callFacts.isEmpty) Some("function(){}")
    else
      val parts = partitionFacts(callFacts)
      val throws = parts.types.exists(_ <= AbruptT) ||
        parts.avoidedTypes.exists(_ <= NormalT)
      if (throws) Some("function(){throw 0;}")
      else
        val returnFacts = dropNormalCompletionFacts(callFacts)
        if (returnFacts.isEmpty) Some("function(){}")
        else renderFacts(returnFacts).map(js => s"function(){return $js;}")

  private def isUndefinedLiteral(lit: LiteralExpr): Boolean = lit match
    case EUndef() => true
    case _        => false

  private def overlaps(left: ValueTy, right: ValueTy): Boolean =
    !(left && right).isBottom

  private def isDirectAbruptCompletion(facts: Set[Fact]): Boolean =
    val parts = partitionFacts(facts)
    parts.types.exists(_ <= AbruptT) &&
    parts.values.isEmpty &&
    parts.excluded.isEmpty &&
    parts.lowers.isEmpty &&
    parts.uppers.isEmpty &&
    parts.props.isEmpty &&
    parts.propExists.isEmpty &&
    parts.calls.isEmpty &&
    parts.extensible.isEmpty &&
    parts.prototypes.isEmpty &&
    parts.traps.isEmpty &&
    parts.fields.isEmpty &&
    parts.fieldExists.isEmpty

  private val abruptConversionObject: String =
    "{[Symbol.toPrimitive](){throw 0}}"

  private case class FactParts(
    values: Set[LiteralExpr],
    excluded: Set[LiteralExpr],
    lowers: Set[(LiteralExpr, Boolean)],
    uppers: Set[(LiteralExpr, Boolean)],
    types: Set[ValueTy],
    avoidedTypes: List[ValueTy],
    props: Map[String, Set[Fact]],
    propExists: Map[String, Set[Boolean]],
    calls: Set[Fact],
    extensible: Set[Boolean],
    prototypes: Set[LiteralExpr],
    traps: Map[String, Set[Fact]],
    fields: Map[String, Set[Fact]],
    fieldExists: Map[String, Set[Boolean]],
  )

  private case class PropertyRender(entry: String, define: String)

  private def partitionFacts(facts: Set[Fact]): FactParts =
    FactParts(
      values = facts.collect { case Fact.Value(lit) => lit },
      excluded = facts.collect { case Fact.NotValue(lit) => lit },
      lowers = facts.collect { case Fact.Lower(lit, strict) => lit -> strict },
      uppers = facts.collect { case Fact.Upper(lit, strict) => lit -> strict },
      types = facts.collect { case Fact.Type(ty) => ty },
      avoidedTypes = facts.collect { case Fact.NotType(ty) => ty }.toList,
      props = facts
        .collect { case Fact.Prop(key, fact) => key -> fact }
        .groupMap(_._1)(_._2)
        .view
        .mapValues(_.toSet)
        .toMap,
      propExists = facts
        .collect { case Fact.PropExists(key, exists) => key -> exists }
        .groupMap(_._1)(_._2)
        .view
        .mapValues(_.toSet)
        .toMap,
      calls = facts.collect { case Fact.Call(fact) => fact },
      extensible = facts.collect { case Fact.Extensible(value) => value },
      prototypes = facts.collect { case Fact.Prototype(lit) => lit },
      traps = facts
        .collect { case Fact.Trap(name, fact) => name -> fact }
        .groupMap(_._1)(_._2)
        .view
        .mapValues(_.toSet)
        .toMap,
      fields = facts
        .collect { case Fact.Field(name, fact) => name -> fact }
        .groupMap(_._1)(_._2)
        .view
        .mapValues(_.toSet)
        .toMap,
      fieldExists = facts
        .collect { case Fact.FieldExists(name, exists) => name -> exists }
        .groupMap(_._1)(_._2)
        .view
        .mapValues(_.toSet)
        .toMap,
    )

  private def renderFacts(facts: Set[Fact]): Option[String] =
    val parts = partitionFacts(facts)
    renderTarget(parts).flatMap(renderTraps(_, parts.traps))

  private def renderTarget(parts: FactParts): Option[String] =
    val structural = hasObjectShape(parts) || parts.calls.nonEmpty
    parts.values.headOption match
      case Some(lit) =>
        if (parts.values.exists(_ != lit) || parts.excluded(lit) || structural)
          None
        else litToJs(lit)
      case None =>
        val requiredTy = requiredValueType(parts)
        val avoidedTys = avoidedValueTypes(parts)
        if (!validInternalFieldExistence(parts)) None
        else if (requiredTy.isBottom) None
        else if (hasNumericBounds(parts))
          renderNumber(parts, requiredTy, avoidedTys)
        else if (parts.fields.nonEmpty || hasRequiredInternalFields(parts))
          renderFieldBackedTarget(parts, requiredTy, avoidedTys)
            .flatMap(renderObjectLike(_, parts))
        else if (parts.calls.nonEmpty)
          renderFunction(parts.calls).flatMap(renderObjectLike(_, parts))
        else if (requiredTy <= FunctionT || requiredTy <= ConstructorT)
          defaultFor(requiredTy, parts.excluded, avoidedTys)
            .flatMap(renderObjectLike(_, parts))
        else if (hasObjectShape(parts))
          val objectTy =
            if ((requiredTy && ObjectT).isBottom) return None
            else requiredTy && ObjectT
          defaultFor(objectTy, parts.excluded, avoidedTys)
            .flatMap(renderObjectLike(_, parts))
        else defaultFor(requiredTy, parts.excluded, avoidedTys)

  private def renderFunction(callFacts: Set[Fact]): Option[String] =
    val parts = partitionFacts(callFacts)
    val throws = parts.types.exists(_ <= AbruptT) ||
      parts.avoidedTypes.exists(_ <= NormalT)
    if (throws) Some("() => { throw 0; }")
    else
      val returnFacts = dropNormalCompletionFacts(callFacts)
      if (returnFacts.isEmpty) Some("() => {}")
      else renderFacts(returnFacts).map(js => s"() => { return $js; }")

  private def dropNormalCompletionFacts(facts: Set[Fact]): Set[Fact] =
    facts.filter {
      case Fact.Type(ty) if ty <= NormalT    => false
      case Fact.NotType(ty) if ty <= AbruptT => false
      case _                                 => true
    }

  private def hasObjectShape(parts: FactParts): Boolean =
    parts.props.nonEmpty ||
    parts.propExists.exists(_._2.contains(true)) ||
    parts.extensible.nonEmpty ||
    parts.prototypes.nonEmpty ||
    parts.fields.nonEmpty ||
    hasRequiredInternalFields(parts)

  private def hasRequiredInternalFields(parts: FactParts): Boolean =
    parts.fieldExists.values.exists(_.contains(true))

  private def validInternalFieldExistence(parts: FactParts): Boolean =
    parts.fieldExists.values.forall(_.size <= 1)

  private def requiredValueType(parts: FactParts): ValueTy =
    parts.types.filterNot(_ <= CompT).foldLeft(ESValueT)(_ && _)

  private def avoidedValueTypes(parts: FactParts): List[ValueTy] =
    parts.avoidedTypes.filterNot(_ <= CompT)

  private def renderObjectLike(
    base: String,
    parts: FactParts,
  ): Option[String] =
    for {
      props <- renderProperties(parts)
      configured <- applyObjectConfig(
        mergeProperties(base, props),
        props,
        parts,
      )
    } yield configured

  private def renderProperties(parts: FactParts): Option[List[PropertyRender]] =
    val rendered = List.newBuilder[PropertyRender]
    val renderedKeys = scala.collection.mutable.Set[String]()
    var failed = false

    for ((key, facts) <- parts.props.toList.sortBy(_._1) if !failed) {
      val existsSet = parts.propExists.getOrElse(key, Set())
      if (existsSet.contains(false)) failed = true
      renderProperty(key, facts) match
        case None => failed = true
        case Some(Some(prop)) =>
          rendered += prop
          renderedKeys += key
        case Some(None) => ()
    }

    for ((key, existsSet) <- parts.propExists.toList.sortBy(_._1) if !failed)
      if (existsSet.size > 1) failed = true
      else if (existsSet.contains(true) && !renderedKeys(key))
        rendered += valueProperty(key, "0")

    if (failed) None else Some(rendered.result())

  private def renderProperty(
    key: String,
    facts: Set[Fact],
  ): Option[Option[PropertyRender]] =
    val parts = partitionFacts(facts)
    val throws = parts.types.exists(_ <= AbruptT) ||
      parts.avoidedTypes.exists(_ <= NormalT)
    if (parts.calls.nonEmpty)
      renderFunction(parts.calls).map(js => Some(valueProperty(key, js)))
    else
      parts.values.headOption match
        case Some(lit) =>
          if (parts.values.exists(_ != lit) || parts.excluded(lit)) None
          else litToJs(lit).map(js => Some(valueProperty(key, js)))
        case None if throws =>
          Some(Some(throwingGetter(key)))
        case None if hasNumericBounds(parts) =>
          renderNumber(
            parts,
            requiredValueType(parts),
            avoidedValueTypes(parts),
          )
            .map(js => Some(valueProperty(key, js)))
        case None if isOnlyNormalCompletion(parts) =>
          Some(None)
        case None if key == "length" =>
          renderArrayLikeLength(parts).map(js => Some(valueProperty(key, js)))
        case None =>
          val requiredTy = requiredValueType(parts)
          val avoidedTys = avoidedValueTypes(parts)
          if (requiredTy.isBottom) None
          else if (hasObjectShape(parts))
            renderTarget(parts).map(js => Some(valueProperty(key, js)))
          else
            defaultFor(requiredTy, parts.excluded, avoidedTys)
              .map(js => Some(valueProperty(key, js)))

  private def isOnlyNormalCompletion(parts: FactParts): Boolean =
    parts.values.isEmpty &&
    parts.excluded.isEmpty &&
    parts.lowers.isEmpty &&
    parts.uppers.isEmpty &&
    parts.props.isEmpty &&
    parts.propExists.isEmpty &&
    parts.calls.isEmpty &&
    parts.extensible.isEmpty &&
    parts.prototypes.isEmpty &&
    parts.traps.isEmpty &&
    parts.fields.isEmpty &&
    parts.fieldExists.isEmpty &&
    parts.types.nonEmpty &&
    parts.types.forall(_ <= NormalT) &&
    parts.avoidedTypes.isEmpty

  private def valueProperty(key: String, js: String): PropertyRender =
    PropertyRender(
      s"${jsPropKey(key)}: $js",
      s"Object.defineProperty(o,${jsKeyLit(key)},{value:$js,writable:true,configurable:true})",
    )

  private def throwingGetter(key: String): PropertyRender =
    PropertyRender(
      s"get ${jsPropKey(key)}() { throw 0; }",
      s"Object.defineProperty(o,${jsKeyLit(key)},{get(){throw 0},configurable:true})",
    )

  private def renderArrayLikeLength(parts: FactParts): Option[String] =
    val requiredTy = requiredValueType(parts)
    val avoidedTys = avoidedValueTypes(parts)
    val canUseNumber =
      (requiredTy == ESValueT || !(requiredTy && NumberT).isBottom) &&
      avoidedTys.forall(avoidTy => (NumberT && avoidTy).isBottom)
    if (canUseNumber)
      List(1, 2, 0)
        .map(n => EMath(BigDecimal(n)))
        .find(lit => !parts.excluded(lit))
        .flatMap(litToJs)
    else defaultFor(requiredTy, parts.excluded, avoidedTys)

  private def mergeProperties(
    base: String,
    props: List[PropertyRender],
  ): String =
    if (props.isEmpty) base
    else if (isObjectLiteral(base))
      val inner = base.drop(1).dropRight(1).trim
      val baseProps = if (inner.isEmpty) Nil else List(inner)
      s"{${(baseProps ++ props.map(_.entry)).mkString(", ")}}"
    else
      val defs = props.map(_.define).mkString(";")
      s"(()=>{var o=$base;$defs;return o})()"

  private def applyObjectConfig(
    js: String,
    props: List[PropertyRender],
    parts: FactParts,
  ): Option[String] =
    val extensible =
      if (parts.extensible.size > 1) return None
      else parts.extensible.headOption
    val prototype =
      if (parts.prototypes.size > 1) return None
      else parts.prototypes.headOption

    val withPrototype = prototype match
      case Some(ENull()) if props.isEmpty && js == "{}" =>
        "Object.create(null)"
      case Some(ENull()) =>
        s"(()=>{var o=$js;Object.setPrototypeOf(o,null);return o})()"
      case Some(_) => return None
      case None    => js

    extensible match
      case Some(false) => Some(s"Object.preventExtensions($withPrototype)")
      case _           => Some(withPrototype)

  private def isObjectLiteral(js: String): Boolean =
    js.startsWith("{") && js.endsWith("}")

  private def renderTraps(
    target: String,
    traps: Map[String, Set[Fact]],
  ): Option[String] =
    if (traps.isEmpty) Some(target)
    else {
      val direct = List.newBuilder[(String, String)]
      val getKeyed = scala.collection.mutable.LinkedHashMap[String, String]()
      val hasKeyed = scala.collection.mutable.LinkedHashMap[String, String]()
      var targetHint = target
      var failed = false

      for ((name, facts) <- traps.toList.sortBy(_._1) if !failed) {
        proxyTrapName.get(name) match
          case None => failed = true
          case Some(trapName) =>
            if (targetHint == "{}") targetHint = proxyTarget(name)
            val directFacts = List.newBuilder[Fact]
            val keyedFacts = scala.collection.mutable
              .LinkedHashMap[String, Set[Fact]]()
            for (fact <- facts)
              fact match
                case Fact.Prop(key, inner)
                    if name == "Get" || name == "HasProperty" =>
                  keyedFacts(key) = keyedFacts.getOrElse(key, Set()) + inner
                case _ =>
                  directFacts += fact

            for ((key, innerFacts) <- keyedFacts if !failed)
              renderKeyedTrapFacts(name, innerFacts) match
                case None => failed = true
                case Some(Some(body)) =>
                  if (name == "Get") getKeyed(key) = body
                  else hasKeyed(key) = body
                case Some(None) => ()

            val directSet = directFacts.result().toSet
            if (directSet.nonEmpty)
              renderInternalMethodTrapFacts(name, directSet) match
                case None             => failed = true
                case Some(Some(body)) => direct += trapName -> body
                case Some(None)       => ()
      }

      if (failed) None
      else {
        val directTraps = direct.result()
        val nonKeyedGet = directTraps.collect {
          case ("get", b) => b
        }.lastOption
        val nonKeyedHas = directTraps.collect {
          case ("has", b) => b
        }.lastOption
        val merged = List.newBuilder[(String, String)]

        for ((name, body) <- directTraps if name != "get" && name != "has")
          merged += name -> body

        if (getKeyed.nonEmpty) {
          val branches = getKeyed
            .map { (key, body) => s"if(${jsKeyCompare(key)}){$body}" }
            .mkString("")
          val fallback = nonKeyedGet.getOrElse("return t[p];")
          merged += "get" -> s"(t,p){$branches$fallback}"
        } else nonKeyedGet.foreach(body => merged += "get" -> body)

        if (hasKeyed.nonEmpty) {
          val branches = hasKeyed
            .map { (key, body) => s"if(${jsKeyCompare(key)}){$body}" }
            .mkString("")
          val fallback = nonKeyedHas.getOrElse("return p in t;")
          merged += "has" -> s"(t,p){$branches$fallback}"
        } else nonKeyedHas.foreach(body => merged += "has" -> body)

        val trapList = merged.result()
        if (trapList.isEmpty) Some(target)
        else {
          val needsNonExtensible = requiresNonExtensibleProxyTarget(traps)
          val finalTarget =
            if (needsNonExtensible)
              s"Object.preventExtensions($targetHint)"
            else targetHint
          val trapStr = trapList
            .map { (name, body) =>
              if (body.startsWith("(")) s"$name$body" else s"$name(){$body}"
            }
            .mkString(", ")
          Some(s"new Proxy($finalTarget, {$trapStr})")
        }
      }
    }

  private def renderKeyedTrapFacts(
    name: String,
    facts: Set[Fact],
  ): Option[Option[String]] =
    if (name == "HasProperty") renderBooleanTrapFacts(facts)
    else renderTrapFacts(facts)

  private def renderTrapFacts(facts: Set[Fact]): Option[Option[String]] =
    val parts = partitionFacts(facts)
    val throws = parts.types.exists(_ <= AbruptT) ||
      parts.avoidedTypes.exists(_ <= NormalT)
    if (throws) Some(Some("throw 0;"))
    else
      val returnFacts = facts.filter {
        case Fact.Type(ty) if ty <= NormalT    => false
        case Fact.NotType(ty) if ty <= AbruptT => false
        case _                                 => true
      }
      if (returnFacts.isEmpty) Some(None)
      else renderFacts(returnFacts).map(js => Some(s"return $js;"))

  private def renderInternalMethodTrapFacts(
    name: String,
    facts: Set[Fact],
  ): Option[Option[String]] =
    if (name == "GetOwnProperty") renderGetOwnPropertyTrapFacts(facts)
    else if (booleanInternalMethods(name)) renderBooleanTrapFacts(facts)
    else renderTrapFacts(facts)

  private def renderBooleanTrapFacts(
    facts: Set[Fact],
  ): Option[Option[String]] =
    val parts = partitionFacts(facts)
    val throws = parts.types.exists(_ <= AbruptT) ||
      parts.avoidedTypes.exists(_ <= NormalT)
    if (throws) Some(Some("throw 0;"))
    else if (parts.values(EBool(true)) && parts.values(EBool(false))) None
    else if (parts.values(EBool(true)) || parts.excluded(EBool(false)))
      Some(Some("return true;"))
    else if (parts.values(EBool(false)) || parts.excluded(EBool(true)))
      Some(Some("return false;"))
    else renderTrapFacts(facts)

  private def requiresNonExtensibleProxyTarget(
    traps: Map[String, Set[Fact]],
  ): Boolean =
    traps.exists {
      case ("PreventExtensions", facts) =>
        booleanFactsAllow(facts, value = true)
      case ("IsExtensible", facts) => booleanFactsAllow(facts, value = false)
      case _                       => false
    }

  private def booleanFactsAllow(facts: Set[Fact], value: Boolean): Boolean =
    val parts = partitionFacts(facts)
    parts.values(EBool(value)) || parts.excluded(EBool(!value))

  private def renderGetOwnPropertyTrapFacts(
    facts: Set[Fact],
  ): Option[Option[String]] =
    val parts = partitionFacts(facts)
    val throws = parts.types.exists(_ <= AbruptT) ||
      parts.avoidedTypes.exists(_ <= NormalT)
    if (throws) Some(Some("throw 0;"))
    else if (parts.values.nonEmpty || parts.props.nonEmpty)
      renderTrapFacts(facts)
    else if (parts.propExists.nonEmpty)
      renderPropertyDescriptor(parts).map(js => Some(s"return $js;"))
    else renderTrapFacts(facts)

  private def renderPropertyDescriptor(parts: FactParts): Option[String] =
    def has(field: String): Option[Boolean] =
      parts.propExists.get(field) match
        case Some(values) if values.size > 1 => None
        case Some(values)                    => Some(values.contains(true))
        case None                            => Some(false)

    for {
      hasValue <- has("Value")
      hasWritable <- has("Writable")
      hasGet <- has("Get")
      hasSet <- has("Set")
      hasEnumerable <- has("Enumerable")
      _ <- has("Configurable")
    } yield {
      val data = hasValue || hasWritable
      val accessor = hasGet || hasSet
      val entries = List.newBuilder[String]
      if (data || !accessor) {
        if (hasValue) entries += "value: 0"
        if (hasWritable) entries += "writable: true"
      } else {
        if (hasGet) entries += "get: function(){}"
        if (hasSet) entries += "set: function(v){}"
      }
      if (hasEnumerable) entries += "enumerable: true"
      val rendered = entries.result()
      val finalEntries = rendered :+ "configurable: true"
      s"{${finalEntries.mkString(", ")}}"
    }

  private case class TypedArrayDefault(
    name: String,
    contentType: String,
    js: String,
  ) {
    val ty: ValueTy = RecordT(name)
  }

  private val typedArrayDefaults: List[TypedArrayDefault] = List(
    TypedArrayDefault("Int8Array", "number", "new Int8Array()"),
    TypedArrayDefault("Uint8Array", "number", "new Uint8Array()"),
    TypedArrayDefault("Uint8ClampedArray", "number", "new Uint8ClampedArray()"),
    TypedArrayDefault("Int16Array", "number", "new Int16Array()"),
    TypedArrayDefault("Uint16Array", "number", "new Uint16Array()"),
    TypedArrayDefault("Int32Array", "number", "new Int32Array()"),
    TypedArrayDefault("Uint32Array", "number", "new Uint32Array()"),
    TypedArrayDefault("BigInt64Array", "bigint", "new BigInt64Array()"),
    TypedArrayDefault("BigUint64Array", "bigint", "new BigUint64Array()"),
    TypedArrayDefault("Float32Array", "number", "new Float32Array()"),
    TypedArrayDefault("Float64Array", "number", "new Float64Array()"),
  )

  private def renderFieldBackedTarget(
    parts: FactParts,
    requiredTy: ValueTy,
    avoidedTys: List[ValueTy],
  ): Option[String] =
    typedArrayDefaults
      .find(candidate =>
        isTypedArrayCandidateAllowed(candidate, parts, requiredTy, avoidedTys),
      )
      .map(_.js)

  private def isTypedArrayCandidateAllowed(
    candidate: TypedArrayDefault,
    parts: FactParts,
    requiredTy: ValueTy,
    avoidedTys: List[ValueTy],
  ): Boolean =
    val candidateTy = candidate.ty
    val typedArrayRelevant =
      !(requiredTy && TypedArrayT).isBottom ||
      parts.fields.contains("TypedArrayName") ||
      parts.fields.contains("ContentType") ||
      parts.fieldExists.get("TypedArrayName").exists(_.contains(true)) ||
      parts.fieldExists.get("ContentType").exists(_.contains(true))
    typedArrayRelevant &&
    !(requiredTy && candidateTy).isBottom &&
    avoidedTys.forall(avoidTy => (candidateTy && avoidTy).isBottom) &&
    parts.fields.forall {
      case ("TypedArrayName", facts) =>
        literalFactsAllow(facts, EStr(candidate.name))
      case ("ContentType", facts) =>
        literalFactsAllow(facts, EEnum(candidate.contentType))
      case _ => false
    } &&
    parts.fieldExists.forall {
      case ("TypedArrayName", existsSet) => existsSet == Set(true)
      case ("ContentType", existsSet)    => existsSet == Set(true)
      case (_, existsSet)                => existsSet == Set(false)
    }

  private def literalFactsAllow(facts: Set[Fact], lit: LiteralExpr): Boolean =
    val parts = partitionFacts(facts)
    parts.values.forall(_ == lit) &&
    !parts.excluded(lit) &&
    parts.lowers.isEmpty &&
    parts.uppers.isEmpty &&
    parts.props.isEmpty &&
    parts.propExists.isEmpty &&
    parts.calls.isEmpty &&
    parts.extensible.isEmpty &&
    parts.prototypes.isEmpty &&
    parts.traps.isEmpty &&
    parts.fields.isEmpty &&
    parts.fieldExists.isEmpty

  private def hasNumericBounds(parts: FactParts): Boolean =
    parts.lowers.nonEmpty || parts.uppers.nonEmpty

  private def renderNumber(
    parts: FactParts,
    requiredTy: ValueTy,
    avoidedTys: List[ValueTy],
  ): Option[String] =
    if ((requiredTy && NumberT).isBottom) None
    else if (avoidedTys.exists(avoidTy => !(NumberT && avoidTy).isBottom)) None
    else pickNumber(parts).flatMap(n => litToJs(EMath(n)))

  private def pickNumber(parts: FactParts): Option[BigDecimal] =
    def parseBounds(
      bounds: Set[(LiteralExpr, Boolean)],
    ): Option[Set[(BigDecimal, Boolean)]] =
      val parsed = bounds.toList.map { (lit, strict) =>
        numValue(lit).map(_ -> strict)
      }
      if (parsed.forall(_.isDefined)) Some(parsed.flatten.toSet) else None

    for {
      lowers <- parseBounds(parts.lowers)
      uppers <- parseBounds(parts.uppers)
      pick <- pickNumber(lowers, uppers, parts.excluded.flatMap(numValue))
    } yield pick

  private def pickNumber(
    lowers: Set[(BigDecimal, Boolean)],
    uppers: Set[(BigDecimal, Boolean)],
    excluded: Set[BigDecimal],
  ): Option[BigDecimal] =
    val lower = lowers.toList.sortBy(_._1).lastOption
    val upper = uppers.toList.sortBy(_._1).headOption

    def valid(v: BigDecimal): Boolean =
      !excluded(v) &&
      lowers.forall((n, strict) => if (strict) n < v else n <= v) &&
      uppers.forall((n, strict) => if (strict) v < n else v <= n)

    val lo = lower
      .map(_._1)
      .getOrElse(upper.map(_._1).getOrElse(BigDecimal(0)) - 100)
    val hi = upper
      .map(_._1)
      .getOrElse(lower.map(_._1).getOrElse(BigDecimal(0)) + 100)
    val intLo = lo.setScale(0, BigDecimal.RoundingMode.CEILING)
    val intHi = hi.setScale(0, BigDecimal.RoundingMode.FLOOR)
    val nearBounds =
      List(
        lower.map((n, strict) => if (strict) n + 1 else n),
        upper.map((n, strict) => if (strict) n - 1 else n),
        Some(BigDecimal(0)),
        Some(BigDecimal(1)),
        Some(BigDecimal(-1)),
      ).flatten.distinct

    nearBounds
      .find(valid)
      .orElse {
        Iterator
          .iterate(intLo)(_ + 1)
          .takeWhile(_ <= intHi)
          .take(200)
          .find(valid)
      }
      .orElse {
        val mid = (lo + hi) / 2
        Option.when(valid(mid))(mid)
      }

  private def numValue(lit: LiteralExpr): Option[BigDecimal] = lit match
    case EMath(n)                                => Some(n)
    case ENumber(d) if !d.isNaN && !d.isInfinite => Some(BigDecimal(d))
    case _                                       => None

  private val wellKnownSymbols: Set[String] = Set(
    "iterator",
    "asyncIterator",
    "hasInstance",
    "isConcatSpreadable",
    "match",
    "matchAll",
    "replace",
    "search",
    "species",
    "split",
    "toPrimitive",
    "toStringTag",
    "unscopables",
  )

  private def jsPropKey(key: String): String =
    JsPropertyKey(key).objectKey

  private def jsKeyLit(key: String): String =
    JsPropertyKey(key).expr

  private def jsKeyCompare(key: String): String =
    JsPropertyKey(key).compare("p")

  private case class JsPropertyKey(key: String) {
    def objectKey: String =
      if (wellKnownSymbols.contains(key)) s"[Symbol.$key]"
      else if (isIdentifierName(key)) key
      else s"[${jsStringLit(key)}]"

    def expr: String =
      if (wellKnownSymbols.contains(key)) s"Symbol.$key"
      else jsStringLit(key)

    def compare(prop: String): String = s"$prop===$expr"
  }

  private case class JsStringProperty(key: String) {
    def expr: String = jsStringLit(key)

    def memberAccess: String =
      if (isIdentifierName(key)) s".$key"
      else s"[$expr]"
  }

  private def isIdentifierName(s: String): Boolean =
    s.nonEmpty &&
    (s.head == '_' || s.head == '$' || s.head.isLetter) &&
    s.tail.forall(c => c == '_' || c == '$' || c.isLetterOrDigit)

  private def jsStringLit(s: String): String =
    val escaped = s.flatMap {
      case '\\'                => "\\\\"
      case '"'                 => "\\\""
      case '\n'                => "\\n"
      case '\r'                => "\\r"
      case '\t'                => "\\t"
      case c if c.toInt < 0x20 => f"\\u${c.toInt}%04x"
      case c                   => c.toString
    }
    s"\"$escaped\""

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

  private val booleanInternalMethods: Set[String] = Set(
    "SetPrototypeOf",
    "IsExtensible",
    "PreventExtensions",
    "DefineOwnProperty",
    "HasProperty",
    "Set",
    "Delete",
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
    case EStr(s)  => Some(jsStringLit(s))
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

  private enum DefaultWitnessKind:
    case SpecificRecord, AbstractValue

  private case class DefaultWitness(
    ty: ValueTy,
    js: String,
    kind: DefaultWitnessKind,
  )

  private object DefaultWitness {
    def record(name: String, js: String): DefaultWitness =
      DefaultWitness(RecordT(name), js, DefaultWitnessKind.SpecificRecord)

    def abstractValue(ty: ValueTy, js: String): DefaultWitness =
      DefaultWitness(ty, js, DefaultWitnessKind.AbstractValue)
  }

  // specific record types: each candidate must be a concrete JS value with the
  // corresponding ECMAScript internal-slot shape.
  private val specificDefaults: List[DefaultWitness] = List(
    DefaultWitness.record("TypedArray", "new Int8Array()"),
    DefaultWitness.record("ArrayIteratorInstance", "[][Symbol.iterator]()"),
    DefaultWitness.record("RegExp", "/./"),
    DefaultWitness.record("BuiltinFunctionObject", "Array.isArray"),
    DefaultWitness.record("BooleanObject", "Object(true)"),
    DefaultWitness.record("NumberObject", "Object(0)"),
    DefaultWitness.record("BigIntObject", "Object(0n)"),
    DefaultWitness.record("StringExoticObject", "Object('')"),
    DefaultWitness.record("Map", "new Map()"),
    DefaultWitness.record("Set", "new Set()"),
    DefaultWitness.record("WeakMap", "new WeakMap()"),
    DefaultWitness.record("WeakSet", "new WeakSet()"),
    DefaultWitness.record("ArrayBuffer", "new ArrayBuffer(0)"),
    DefaultWitness.record("DataView", "new DataView(new ArrayBuffer(0))"),
    DefaultWitness.record("Date", "new Date()"),
    DefaultWitness.record("Promise", "new Promise(() => {})"),
    DefaultWitness.record("ErrorObject", "new Error()"),
    DefaultWitness.record("Generator", "(function*(){})()"),
    DefaultWitness.record("AsyncGenerator", "(async function*(){})()"),
    DefaultWitness.record("WeakRef", "new WeakRef({})"),
    DefaultWitness
      .record("FinalizationRegistry", "new FinalizationRegistry(() => {})"),
    DefaultWitness.record("ProxyExoticObject", "new Proxy({}, {})"),
    DefaultWitness.record("BoundFunctionExoticObject", "(function(){}).bind()"),
    DefaultWitness.record("Array", "[]"),
  )

  // abstract types (primitives + general object categories)
  private val abstractDefaults: List[DefaultWitness] = List(
    DefaultWitness.abstractValue(ConstructorT, "function(){}"),
    DefaultWitness.abstractValue(FunctionT, "() => {}"),
    DefaultWitness.abstractValue(NumberT, "0"),
    DefaultWitness.abstractValue(StrT, "\"\""),
    DefaultWitness.abstractValue(BoolT, "true"),
    DefaultWitness.abstractValue(NullT, "null"),
    DefaultWitness.abstractValue(UndefT, "undefined"),
    DefaultWitness.abstractValue(BigIntT, "0n"),
    DefaultWitness.abstractValue(SymbolT, "Symbol()"),
    DefaultWitness.abstractValue(ObjectT, "{}"),
  )

  // all candidates: specific first (for exact match)
  private val defaults = specificDefaults ++ abstractDefaults

  private def defaultFor(
    ty: ValueTy,
    excluded: Set[LiteralExpr] = Set(),
    avoidTys: List[ValueTy] = Nil,
  ): Option[String] =
    val excJs = excluded.flatMap(litToJs)
    def allowed(candidateTy: ValueTy, js: String): Boolean =
      !excJs(js) && avoidTys.forall(avoidTy =>
        (candidateTy && avoidTy).isBottom,
      )
    // 1. exact match
    defaults
      .collectFirst {
        case candidate
            if (ty <= candidate.ty) &&
            (candidate.ty <= ty) &&
            allowed(candidate.ty, candidate.js) =>
          candidate.js
      }
      .orElse {
        // 2. specific intersection for narrow object types
        if (ty <= ObjectT && !(ObjectT <= ty))
          specificDefaults.collectFirst {
            case candidate
                if !(ty && candidate.ty).isBottom &&
                allowed(candidate.ty, candidate.js) =>
              candidate.js
          }
        else None
      }
      .orElse {
        // 3. abstract subtype match
        abstractDefaults.collectFirst {
          case candidate
              if ty <= candidate.ty && allowed(candidate.ty, candidate.js) =>
            candidate.js
        }
      }
      .orElse {
        // 4. abstract intersection match
        abstractDefaults.collectFirst {
          case candidate
              if !(ty && candidate.ty).isBottom &&
              allowed(candidate.ty, candidate.js) =>
            candidate.js
        }
      }
      .orElse {
        // 5. fallback for excluded primitive defaults
        if (ty <= NumberT)
          List("1", "-1", "0.5", "2", "100").find(allowed(NumberT, _))
        else if (ty <= StrT)
          List("\"a\"", "\"test\"").find(allowed(StrT, _))
        else None
      }

  // reverse index: field name -> union of record types that always have it
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

  private def propKey(e: SymExpr): Option[String] = e match
    case SELit(EStr(s)) => Some(s)
    case SELit(EMath(n)) if n.isValidInt && n >= 0 =>
      Some(n.toInt.toString)
    case SELit(ENumber(d)) if d >= 0 && d == d.toLong && !d.isInfinite =>
      Some(d.toLong.toString)
    case _ => None

  // normalize FEq so non-literal term is always on the left
  private def normalizeEq(f: Formula): Formula = f match
    case FEq(l: SELit, r) if !r.isInstanceOf[SELit]       => FEq(r, l)
    case FNot(FEq(l: SELit, r)) if !r.isInstanceOf[SELit] => FNot(FEq(r, l))
    case FNot(inner) => FNot(normalizeEq(inner))
    case _           => f

  def hasUninterpretableApp(fs: List[Formula]): Boolean =
    def fromExpr(t: SymExpr): Set[String] = t match
      case SEApp(fname: String, args) => Set(fname) ++ args.flatMap(fromExpr)
      case SEApp(_, args)             => args.flatMap(fromExpr).toSet
      case SEProj(base, key)          => fromExpr(base) ++ fromExpr(key)
      case SEField(base, _)           => fromExpr(base)
      case SEList(elems)              => elems.flatMap(fromExpr).toSet
      case SERecord(_, fs)            => fs.values.flatMap(fromExpr).toSet
      case SEMap(es) =>
        es.flatMap((k, v) => fromExpr(k) ++ fromExpr(v)).toSet
      case SETypeOf(t) => fromExpr(t)
      case _           => Set()
    def fromFormula(f: Formula): Set[String] = f match
      case FNot(inner)      => fromFormula(inner)
      case FEq(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FLt(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FExists(b, _)    => fromExpr(b)
      case FTypeCheck(e, _) => fromExpr(e)
    fs.exists(fromFormula(_).exists(!isKnownApp(_)))

  def outerAppNames(f: Formula): Set[String] =
    def fromExpr(t: SymExpr): Set[String] = t match
      case SEApp(fname: String, _) if !isKnownApp(fname) => Set(fname)
      case SEApp(_, args)    => args.flatMap(fromExpr).toSet
      case SEProj(base, key) => fromExpr(base) ++ fromExpr(key)
      case SEField(base, _)  => fromExpr(base)
      case SEList(elems)     => elems.flatMap(fromExpr).toSet
      case SERecord(_, fs)   => fs.values.flatMap(fromExpr).toSet
      case SEMap(es) =>
        es.flatMap((k, v) => fromExpr(k) ++ fromExpr(v)).toSet
      case SETypeOf(t) => fromExpr(t)
      case _           => Set()
    f match
      case FNot(inner)      => outerAppNames(inner)
      case FEq(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FLt(l, r)        => fromExpr(l) ++ fromExpr(r)
      case FExists(b, _)    => fromExpr(b)
      case FTypeCheck(e, _) => fromExpr(e)

  private def isKnownApp(name: String): Boolean =
    internalMethods.contains(name)

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
      s"Object.getOwnPropertyDescriptor(${pathStr(owner)}, ${JsStringProperty(prop).expr})"
    case BuiltinPath.SymbolAccess(owner, sym) =>
      s"Object.getOwnPropertyDescriptor(${pathStr(owner)}, Symbol.$sym)"
    case _ => "undefined"

  private def pathStr(path: BuiltinPath): String = path match
    case BuiltinPath.Base(name) => globalAlias.getOrElse(name, name)
    case BuiltinPath.NormalAccess(base, name) =>
      s"${pathStr(base)}${JsStringProperty(name).memberAccess}"
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
