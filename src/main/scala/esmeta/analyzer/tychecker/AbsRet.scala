package esmeta.analyzer.tychecker

import esmeta.util.Appender.*

/** abstract return values */
trait AbsRetDecl { self: TyChecker =>

  case class AbsRet(values: Map[NodePoint[?], AbsValue]) extends AbsRetLike {
    import AbsRet.*

    /** bottom check */
    def isBottom: Boolean = values.forall { case (_, v) => v.isBottom }

    def value(using AbsState): AbsValue =
      values.values.foldLeft(AbsValue.Bot)(_ ⊔ _)

    def apply(np: NodePoint[?]): AbsValue = values.getOrElse(np, AbsValue.Bot)

    /** partial order */
    def ⊑(that: AbsRet)(using AbsState): Boolean =
      val keys = this.values.keySet ++ that.values.keySet
      keys.forall(k => this(k) ⊑ that(k))

    /** not partial order */
    def !⊑(that: AbsRet)(using AbsState): Boolean = !(this ⊑ that)

    /** join operator */
    def ⊔(that: AbsRet)(using AbsState): AbsRet =
      val keys = this.values.keySet ++ that.values.keySet
      AbsRet(keys.map(k => k -> (this(k) ⊔ that(k))).toMap)

    /** meet operator */
    def ⊓(that: AbsRet)(using AbsState): AbsRet =
      val keys = this.values.keySet ++ that.values.keySet
      AbsRet(keys.map(k => k -> (this(k) ⊓ that(k))).toMap)
  }
  object AbsRet extends DomainLike[AbsRet] {

    /** top element */
    lazy val Top: AbsRet = AbsRet(Map.empty.withDefaultValue(AbsValue.Top))

    /** bottom element */
    lazy val Bot: AbsRet = AbsRet(Map.empty)

    /** appender */
    given rule: Rule[AbsRet] = (app, elem) =>
      given Rule[(NodePoint[?], AbsValue)] = {
        case (app, (np, value)) => app >> value >> " @ [" >> np.node.id >> "]"
      }
      given Rule[Iterable[(NodePoint[?], AbsValue)]] = iterableRule(sep = " | ")
      app >> elem.values.toList.sortBy(_._1.node.id)
  }
}
