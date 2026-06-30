package esmeta.analyzer.tychecker

import esmeta.cfg.*
import esmeta.ir.{Func => _, *}
import esmeta.ty.*
import esmeta.util.{*, given}
import esmeta.util.Appender.*
import esmeta.util.BaseUtils.*
import esmeta.util.SystemUtils.exists

/** type guards */
trait TypeGuardDecl { self: TyChecker =>

  /** type guard */
  case class TypeGuard(map: Map[TargetType, TypeConstr] = Map()) {
    def isEmpty: Boolean = map.isEmpty
    def nonEmpty: Boolean = !isEmpty
    def dtys: Set[TargetType] = map.keySet

    def apply(dty: TargetType): TypeConstr =
      map.getOrElse(dty, TypeConstr.Top)

    def bases: Set[Base] = map.values.flatMap(_.bases).toSet

    def kill(bases: Set[Base])(using AbsState): TypeGuard = TypeGuard(for {
      (dty, constr) <- map
      newConstr = constr.kill(bases)
      if !newConstr.isTop
    } yield dty -> newConstr)

    def filter(ty: ValueTy): TypeGuard =
      TypeGuard(map.filter { (dty, _) => dty.ty overlap ty })

    def has(x: Base): Boolean = map.values.exists(_.has(x))

    def derive(fromTy: ValueTy, toTy: ValueTy): TypeConstr =
      val ty = fromTy && toTy
      map
        .collect { case (dty, constr) if ty <= dty.ty => constr }
        .foldLeft(TypeConstr.Top)(_ && _)

    def hasLocal: Boolean = map.values.exists(_.hasLocal)

    def hasSym: Boolean = map.values.exists(_.hasSym)

    def onlySym: TypeGuard = TypeGuard(
      map.map { (dty, constr) => dty -> constr.onlySym },
    )

    def normalized(upper: ValueTy): TypeGuard = TypeGuard(
      map.filter((dty, constr) => (dty.ty overlap upper) && !constr.isTop),
    )

    override def toString: String = (new Appender >> this).toString
  }
  object TypeGuard {
    val Empty: TypeGuard = TypeGuard()
    def apply(ps: (TargetType, TypeConstr)*): TypeGuard = TypeGuard(
      ps.toMap,
    )
  }
  extension (lpair: (ValueTy, TypeGuard)) {
    def <=(rpair: (ValueTy, TypeGuard)): Boolean = {
      val (luty, lguard) = lpair
      val (ruty, rguard) = rpair
      luty <= ruty &&
      rguard.map.forall { (dty, constr) =>
        (luty distinct dty.ty) || lguard(dty) <= constr
      }
    }
    def ||(rpair: (ValueTy, TypeGuard)): TypeGuard = {
      val (luty, lguard) = lpair
      val (ruty, rguard) = rpair
      val ty = luty || ruty
      TypeGuard(
        (for {
          dty <- (lguard.dtys ++ rguard.dtys).toList
          constr = {
            (if (dty.ty overlap luty) lguard(dty) else TypeConstr.Bot) ||
            (if (dty.ty overlap ruty) rguard(dty) else TypeConstr.Bot)
          }
          if !constr.isTop
        } yield dty -> constr).toMap,
      )
    }
    def &&(rpair: (ValueTy, TypeGuard)): TypeGuard = {
      val (luty, lguard) = lpair
      val (ruty, rguard) = rpair
      val ty = luty && ruty
      TypeGuard(
        (for {
          dty <- (lguard.dtys ++ rguard.dtys).toList
          if dty.ty overlap ty
          constr = lguard(dty) && rguard(dty)
        } yield dty -> constr).toMap,
      )
    }
    def add(constr: TypeConstr): TypeGuard =
      val (uty, guard) = lpair
      TypeGuard(
        TargetType.from(uty).map(dty => dty -> (guard(dty) && constr)).toMap,
      )
  }

  case class TargetType(ty: ValueTy)

  object TargetType {
    val all: List[ValueTy] = List(
      TrueT,
      FalseT,
      NormalT,
      AbruptT,
      NormalT(TrueT),
      NormalT(FalseT),
      ENUMT_SYNC,
      ENUMT_ASYNC,
    )
    val set: Set[ValueTy] = all.toSet

    def from(givenTy: ValueTy): List[TargetType] =
      TargetType.all.filter(givenTy overlap _).map(TargetType(_))
  }

  /** type constraints */
  enum TypeConstr {
    case Bot
    case Elem(map: Map[Base, ValueTy])

    import TypeConstr.*
    def isTop: Boolean = this == Top
    def isBottom: Boolean = this == Bot

    def get(x: Base): ValueTy = this match
      case Bot       => BotT
      case Elem(map) => map.getOrElse(x, AnyT)

    def map(f: Map[Base, ValueTy] => Map[Base, ValueTy]): TypeConstr =
      this match
        case Bot       => Bot
        case Elem(map) => Elem(f(map))

    def fold[T](default: => T)(f: Map[Base, ValueTy] => T): T = this match
      case Bot       => default
      case Elem(map) => f(map)

    def forall(f: Map[Base, ValueTy] => Boolean): Boolean = this match
      case Bot       => true
      case Elem(map) => f(map)

    def exists(f: Map[Base, ValueTy] => Boolean): Boolean = this match
      case Bot       => false
      case Elem(map) => f(map)

    def <=(that: TypeConstr): Boolean = (this, that) match
      case (Bot, _) => true
      case (_, Bot) => true
      case (Elem(lmap), Elem(rmap)) =>
        rmap.forall { case (r, rty) => lmap.get(r).fold(false) { _ <= rty } }

    def ||(that: TypeConstr): TypeConstr = (this, that) match
      case (Bot, _) => that
      case (_, Bot) => this
      case (Elem(lmap), Elem(rmap)) =>
        Elem((for {
          x <- (lmap.keySet intersect rmap.keySet).toList
          lty = lmap(x)
          rty = rmap(x)
          pair = {
            if (lty <= rty) rty
            else if (rty <= lty) lty
            else lty || rty
          }
        } yield x -> pair).toMap)

    def &&(that: TypeConstr): TypeConstr = (this, that) match
      case (Bot, _) | (_, Bot) => Bot
      case (Elem(lmap), Elem(rmap)) =>
        Elem((for {
          x <- (lmap.keySet ++ rmap.keySet).toList
          lty = lmap.getOrElse(x, AnyT)
          rty = rmap.getOrElse(x, AnyT)
          pair = {
            if (lty <= rty) lty
            else if (rty <= lty) rty
            else lty && rty
          }
        } yield x -> pair).toMap)

    def has(x: Base): Boolean = exists(_.contains(x))

    def bases: Set[Base] = this match
      case Bot       => Set()
      case Elem(map) => map.keySet.collect { case s: Sym => s }

    def kill(bases: Set[Base])(using AbsState): TypeConstr =
      map(_.filter { case (x, _) => !bases.contains(x) })

    def lift(using st: AbsState): TypeConstr = this && st.constr

    def hasLocal: Boolean = exists(_.keySet.exists {
      case _: Local => true
      case _        => false
    })

    def hasSym: Boolean = exists(_.keySet.exists {
      case s: Sym => true
      case _      => false
    })

    def onlySym: TypeConstr =
      map(_.collect { case (x: Sym, ty) => x -> ty })

    override def toString: String = (new Appender >> this).toString
  }
  object TypeConstr {
    val Top: TypeConstr = Elem(Map())
    def apply(pairs: (Base, ValueTy)*): TypeConstr = Elem(pairs.toMap)
  }
  // -----------------------------------------------------------------------------
  // helpers
  // -----------------------------------------------------------------------------
  import tyStringifier.given

  /** TypeGuard */
  given Rule[TypeGuard] = (app, guard) =>
    given Ordering[TargetType] = Ordering.by(_.toString)
    given Rule[TargetType] = (app, dty) => app >> dty.ty
    given Rule[Map[TargetType, TypeConstr]] = sortedMapRule("{", "}", " => ")
    app >> guard.map

  /** TypeConstr */
  given Rule[TypeConstr] = (app, constr) =>
    import TypeConstr.*
    import SymTy.given
    given Rule[Map[Base, ValueTy]] = sortedMapRule(sep = ": ")
    constr match
      case Bot => app >> "⊥"
      case Elem(map) =>
        if (map.nonEmpty) app >> map
        app

}
