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
  case class TypeGuard(map: Map[TargetType, MayMust] = Map()) {
    def isEmpty: Boolean = map.isEmpty
    def nonEmpty: Boolean = !isEmpty
    def dtys: Set[TargetType] = map.keySet

    def apply(dty: TargetType): MayMust = map.getOrElse(dty, MayMust.Must)

    def bases: Set[Base] = map.values.flatMap(_.bases).toSet

    def kill(bases: Set[Base])(using AbsState): TypeGuard = TypeGuard(for {
      (dty, mayMust) <- map
      newMayMust = mayMust.kill(bases)
      if !newMayMust.isTop
    } yield dty -> newMayMust)

    def filter(ty: ValueTy): TypeGuard =
      TypeGuard(map.filter { (dty, _) => dty.ty overlap ty })

    def has(x: Base): Boolean = map.values.exists(_.has(x))

    def derive(fromTy: ValueTy, toTy: ValueTy): MayMust =
      val ty = fromTy && toTy
      map
        .collect { case (dty, mayMust) if ty <= dty.ty => mayMust }
        .foldLeft(MayMust.Must)(_ && _)

    def hasLocal: Boolean = map.values.exists(_.hasLocal)

    def hasSym: Boolean = map.values.exists(_.hasSym)

    def onlySym: TypeGuard = TypeGuard(
      map.map { (dty, mayMust) => dty -> mayMust.onlySym },
    )

    def normalized(upper: ValueTy): TypeGuard = TypeGuard(
      map.filter((dty, mayMust) => (dty.ty overlap upper) && !mayMust.isTop),
    )

    override def toString: String = (new Appender >> this).toString
  }
  object TypeGuard {
    val Empty: TypeGuard = TypeGuard()
    def apply(ps: (TargetType, MayMust)*): TypeGuard = TypeGuard(
      ps.toMap,
    )
  }
  extension (lpair: (ValueTy, TypeGuard)) {
    def <=(rpair: (ValueTy, TypeGuard)): Boolean = {
      val (luty, lguard) = lpair
      val (ruty, rguard) = rpair
      luty <= ruty &&
      rguard.map.forall { (dty, mayMust) =>
        (luty distinct dty.ty) || lguard(dty) <= mayMust
      }
    }
    def ||(rpair: (ValueTy, TypeGuard)): TypeGuard = {
      val (luty, lguard) = lpair
      val (ruty, rguard) = rpair
      val ty = luty || ruty
      TypeGuard(
        (for {
          dty <- (lguard.dtys ++ rguard.dtys).toList
          mayMust = {
            (if (dty.ty overlap luty) lguard(dty) else MayMust.Bot) ||
            (if (dty.ty overlap ruty) rguard(dty) else MayMust.Bot)
          }
          if !mayMust.isTop
        } yield dty -> mayMust).toMap,
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
          mayMust = lguard(dty) && rguard(dty)
        } yield dty -> mayMust).toMap,
      )
    }
    def add(mayMust: MayMust): TypeGuard =
      val (uty, guard) = lpair
      TypeGuard(
        TargetType.from(uty).map(dty => dty -> (guard(dty) && mayMust)).toMap,
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

    def toMay: MayMust = MayMust(this, TypeConstr.Bot)
    def toMayMust: MayMust = MayMust(this, this)
    def toMust: MayMust = MayMust(TypeConstr.Top, this)

    def has(x: Base): Boolean = exists(_.contains(x))

    def bases: Set[Base] = this match
      case Bot       => Set()
      case Elem(map) => map.keySet.collect { case s: Sym => s }

    def kill(bases: Set[Base])(using AbsState): TypeConstr =
      map(_.filter { case (x, _) => !bases.contains(x) })

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

  case class MayMust(may: TypeConstr, must: TypeConstr) {
    def isTop: Boolean = may.isTop && must.isTop
    def isBottom: Boolean = may.isBottom && must.isBottom
    def <=(that: MayMust): Boolean =
      this.may <= that.may && this.must <= that.must
    def &&(that: MayMust): MayMust =
      MayMust(this.may && that.may, this.must && that.must)
    def ||(that: MayMust): MayMust =
      MayMust(this.may || that.may, this.must || that.must)

    def dropMust: MayMust = MayMust(may, TypeConstr.Bot)

    def map(f: TypeConstr => TypeConstr): MayMust =
      MayMust(f(may), f(must))

    def has(x: Base): Boolean = may.has(x) || must.has(x)

    def bases: Set[Base] = may.bases ++ must.bases

    def kill(bases: Set[Base])(using AbsState): MayMust = map(_.kill(bases))

    def lift(using st: AbsState): MayMust = this && st.mayMust

    def hasLocal: Boolean = may.hasLocal || must.hasLocal

    def hasSym: Boolean = may.hasSym || must.hasSym

    def onlySym: MayMust = map(_.onlySym)
  }
  object MayMust {
    val Bot: MayMust = MayMust(TypeConstr.Bot, TypeConstr.Bot)
    val Must: MayMust = MayMust(TypeConstr.Top, TypeConstr.Top)
    val May: MayMust = MayMust(TypeConstr.Top, TypeConstr.Bot)
  }

  /** symbolic expressions */
  enum SymExpr {
    case SEBool(b: Boolean)
    case SERef(ref: SymRef)
    case SEExists(ref: SymRef)
    case SETypeCheck(base: SymExpr, ty: ValueTy)
    case SETypeOf(base: SymExpr)
    case SEEq(left: SymExpr, right: SymExpr)
    def ||(that: SymExpr): SymExpr = (this, that) match
      case _ if this == that                     => this
      case (SEBool(false), _)                    => that
      case (_, SEBool(false))                    => this
      case (SEBool(true), _) | (_, SEBool(true)) => SEBool(true)
      case _                                     => SEBool(true)
    def &&(that: SymExpr): SymExpr = (this, that) match
      case _ if this == that                       => this
      case (SEBool(true), _)                       => that
      case (_, SEBool(true))                       => this
      case (SEBool(false), _) | (_, SEBool(false)) => SEBool(false)
      case _                                       => SEBool(true)
    def has(x: Base): Boolean = this match
      case SEBool(b)             => false
      case SERef(ref)            => ref.has(x)
      case SEExists(ref)         => ref.has(x)
      case SETypeCheck(base, ty) => base.has(x)
      case SETypeOf(base)        => base.has(x)
      case SEEq(left, right)     => left.has(x) || right.has(x)
    def bases: Set[Base] = this match
      case SEBool(b)             => Set()
      case SERef(ref)            => ref.bases
      case SEExists(ref)         => ref.bases
      case SETypeCheck(base, ty) => base.bases
      case SETypeOf(base)        => base.bases
      case SEEq(left, right)     => left.bases ++ right.bases
    def kill(bases: Set[Base]): Option[SymExpr] = this match
      case SEBool(b) => Some(this)
      case SERef(ref) =>
        ref.killRef(ref, bases, true).map(SERef(_)) // FIXME: check later
      case SEExists(ref) => ref.killRef(ref, bases, true).map(SEExists(_))
      case SETypeCheck(base, ty) => base.kill(bases).map(SETypeCheck(_, ty))
      case SETypeOf(base)        => base.kill(bases).map(SETypeOf(_))
      case SEEq(left, right) =>
        for {
          l <- left.kill(bases)
          r <- right.kill(bases)
        } yield SEEq(l, r)
    override def toString: String = (new Appender >> this).toString
  }
  object SymExpr {
    // val T: SymExpr = SEBool(true)
    // val F: SymExpr = SEBool(false)
    extension (l: Option[SymExpr])
      def &&(
        r: Option[SymExpr],
      ): Option[SymExpr] = (l, r) match
        case (Some(le), Some(re)) => Some(le && re)
        case (Some(l), None)      => Some(l)
        case (None, Some(r))      => Some(r)
        case _                    => None
      def ||(
        r: Option[SymExpr],
      ): Option[SymExpr] = (l, r) match
        case (Some(le), Some(re)) => Some(le || re)
        case _                    => None
  }
  // -----------------------------------------------------------------------------
  // helpers
  // -----------------------------------------------------------------------------
  import tyStringifier.given

  /** SymExpr */
  private def symExprRule(app: Appender, expr: SymExpr): Appender =
    import SymExpr.*
    expr match
      case SEBool(bool)  => app >> bool
      case SERef(ref)    => app >> ref
      case SEExists(ref) => app >> "(exists " >> ref >> ")"
      case SETypeCheck(e, ty) =>
        symExprRule(app >> "(? ", e) >> ": " >> ty >> ")"
      case SETypeOf(base) => symExprRule(app >> "(typeof ", base) >> ")"
      case SEEq(left, right) =>
        val a = symExprRule(app >> "(= ", left)
        symExprRule(a >> " ", right) >> ")"

  // Expose the helper as the given instance, avoiding self-referential implicit search issues.
  given Rule[SymExpr] = symExprRule

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

  /** MayMust */
  given Rule[MayMust] = (app, mayMust) =>
    import MayMust.*
    app >> mayMust.may
    if (mayMust.may != mayMust.must)
      app >> " (MUST: " >> mayMust.must >> ")"
    app
}
