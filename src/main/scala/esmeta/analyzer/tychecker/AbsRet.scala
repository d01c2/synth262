package esmeta.analyzer.tychecker

import esmeta.util.Appender.*

/** abstract return values */
trait AbsRetDecl { self: TyChecker =>

  case class AbsRet(
    value: AbsValue = AbsValue.Bot,
    noSym: AbsValue = AbsValue.Bot,
    syms: Map[NodePoint[?], (AbsValue, TypeConstr)] = Map.empty,
  ) extends AbsRetLike {
    import AbsRet.*

    /** bottom check */
    def isBottom: Boolean = value.isBottom

    /** partial order */
    def ⊑(that: AbsRet)(using AbsState): Boolean = ???

    /** not partial order */
    def !⊑(that: AbsRet)(using AbsState): Boolean = ???

    /** join operator */
    def ⊔(that: AbsRet)(using AbsState): AbsRet = ???

    /** meet operator */
    def ⊓(that: AbsRet)(using AbsState): AbsRet = ???
  }
  object AbsRet extends DomainLike[AbsRet] {

    /** top element */
    lazy val Top: AbsRet = AbsRet(AbsValue.Top)

    /** bottom element */
    lazy val Bot: AbsRet = AbsRet(AbsValue.Bot)

    /** appender */
    given rule: Rule[AbsRet] = (app, elem) =>
      (app >> elem.noSym).wrap {
        for ((np, (v, constr)) <- elem.syms.toList.sortBy(_._1.node.id))
          app :> np.node.name >> " -> " >> v >> " (" >> constr >> ")"
      }
  }
}
