package esmeta.fuzzer.synthesizer

import esmeta.cfg.CFG
import esmeta.es.*

object Util {
  // ---------------------------------------------------------------------------
  // ObjectLiteral AST manipulation
  // ---------------------------------------------------------------------------

  def getProps(obj: Syntactic): List[Ast] = obj match
    case Syntactic("ObjectLiteral", _, 1 | 2, children) =>
      flattenPropList(children(0).get)
    case _ => List()

  def withProps(props: List[Ast], args: List[Boolean]): Syntactic =
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
    case _ => List()

  private def buildPropList(
    props: List[Ast],
    args: List[Boolean],
  ): Syntactic =
    val (rhsIdx, children) =
      if (props.init.isEmpty) (0, Vector(Some(props.last)))
      else (1, Vector(Some(buildPropList(props.init, args)), Some(props.last)))
    Syntactic("PropertyDefinitionList", args, rhsIdx, children)

  def findObjectLiteral(ast: Ast): Option[Syntactic] = ast match
    case s @ Syntactic("ObjectLiteral", _, _, _) => Some(s)
    case Syntactic(_, _, _, children) =>
      children.flatten.flatMap(findObjectLiteral).headOption
    case _ => None

  def findTopLevelObjectLiterals(ast: Ast): List[Syntactic] = ast match
    case s @ Syntactic("ObjectLiteral", _, _, _) => List(s)
    case Syntactic(_, _, _, children) =>
      children.flatten.flatMap(findTopLevelObjectLiterals).toList
    case _ => List()

  /** replace a specific Syntactic node inside an AST (by reference equality) */
  def replaceSyntactic(
    ast: Syntactic,
    target: Syntactic,
    replacement: Syntactic,
  ): Option[Syntactic] =
    if (ast eq target) Some(replacement)
    else
      var found = false
      val newChildren = ast.children.map(_.map { child =>
        if (found) child
        else
          child match
            case s: Syntactic =>
              replaceSyntactic(s, target, replacement) match
                case Some(modified) => found = true; modified
                case None           => child
            case _ => child
      })
      if (found) Some(Syntactic(ast.name, ast.args, ast.rhsIdx, newChildren))
      else None

  /** Collect all Syntactic nodes in pre-order traversal */
  def enumerateNodes(ast: Syntactic): List[Syntactic] =
    ast :: ast.children.flatten
      .collect { case s: Syntactic => enumerateNodes(s) }
      .flatten
      .toList

  def propKey(pd: Ast)(using cfg: CFG): Option[String] = pd match
    case Syntactic("PropertyDefinition", _, 0, children) =>
      children(0).map(_.toString(grammar = Some(cfg.grammar)).trim)
    case Syntactic(_, _, _, children) =>
      children.flatten.collectFirst {
        case s @ Syntactic("LiteralPropertyName", _, _, cs) =>
          cs(0).map(_.toString(grammar = Some(cfg.grammar)).trim)
      }.flatten
    case _ => None

  // ---------------------------------------------------------------------------
  // Property injection/ejection
  // ---------------------------------------------------------------------------

  /** inject a raw property definition string into ObjectLiterals */
  def injectPropDef(
    propDefStr: String,
    args: List[Boolean],
    into: Option[Syntactic],
  )(using cfg: CFG): List[Syntactic] = try {
    val parsed = cfg
      .esParser("PrimaryExpression", args)
      .from(s"{ $propDefStr }")
      .asInstanceOf[Syntactic]
    (for {
      obj <- findObjectLiteral(parsed)
      propDef <- getProps(obj).headOption
    } yield into match
      case Some(target: Syntactic) if target.name == "ObjectLiteral" =>
        List(withProps(getProps(target) :+ propDef, target.args))
      case Some(target: Syntactic) =>
        findTopLevelObjectLiterals(target).flatMap { inner =>
          replaceSyntactic(
            target,
            inner,
            withProps(getProps(inner) :+ propDef, inner.args),
          ).toList
        }
      case None => List(withProps(List(propDef), args))
    ).getOrElse(List())
  } catch { case _: Exception => List() }

  /** remove a property from an existing ObjectLiteral */
  def ejectPropDef(
    prop: String,
    from: Syntactic,
  )(using cfg: CFG): List[Syntactic] =
    if (from.name == "ObjectLiteral")
      val props = getProps(from)
      val filtered = props.filterNot(propDef => propKey(propDef).contains(prop))
      if (filtered.length == props.length) List()
      else List(withProps(filtered, from.args))
    else
      findTopLevelObjectLiterals(from).flatMap { inner =>
        val props = getProps(inner)
        val filtered =
          props.filterNot(propDef => propKey(propDef).contains(prop))
        if (filtered.length == props.length) List()
        else
          replaceSyntactic(
            from,
            inner,
            withProps(filtered, inner.args),
          ).toList
      }
}
