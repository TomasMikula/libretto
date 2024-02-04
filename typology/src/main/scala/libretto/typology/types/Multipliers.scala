package libretto.typology.types

import libretto.lambda.{PairwiseRel, Projection, StrongZippable, UnhandledCase}
import libretto.lambda.util.{Exists, ExistsCo, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.typology.types.kindShuffle.~⚬

sealed trait Multipliers[A, AA] {
  def after[A0](m: Multiplier[×, A0, A])(using Kind[A0]): Multiplier[×, A0, AA]

  def >[BB](that: Multipliers[AA, BB]): Multipliers[A, BB]

  def apply[F[_]](fa: F[A])(using StrongZippable[×, F]): F[AA]

  def project[BB](
    p: Projection[×, AA, BB],
  ): ExistsCo[[B] =>> (Projection[×, A, B], Multipliers[B, BB])]

  def preShuffle[Z](s: Z ~⚬ A): ExistsCo[[ZZ] =>> (Multipliers[Z, ZZ], ZZ ~⚬ AA)]

  def from[Z](using ev: Z =:= A): Multipliers[Z, AA] =
    ev.substituteContra[Multipliers[_, AA]](this)

  def to[BB](using ev: AA =:= BB): Multipliers[A, BB] =
    ev.substituteCo(this)

  def proper(using KindN[A]): Multipliers.Proper[A, AA] =
    this match
      case p: Multipliers.Proper[a, aa] => p
      case Multipliers.None => KindN.cannotBeUnit(KindN[A])
}

object Multipliers {
  case object None extends Multipliers[○, ○] {
    override def after[A0](m: Multiplier[×, A0, ○])(using Kind[A0]): Multiplier[×, A0, ○] =
      m

    override def >[BB](that: Multipliers[○, BB]): Multipliers[○, BB] =
      that

    override def apply[F[_]](fa: F[○])(using StrongZippable[×, F]): F[○] =
      fa

    override def project[BB](
      p: Projection[×, ○, BB],
    ): Exists[[B] =>> (Projection[×, ○, B], Multipliers[B, BB])] =
      UnhandledCase.raise(s"$this.project($p)")

    override def preShuffle[Z](s: Z ~⚬ ○): Exists[[ZZ] =>> (Multipliers[Z, ZZ], ZZ ~⚬ ○)] =
      given (Z =:= ○) = s.proveIdBw(Kinds.unitIsNotPair)
      Exists((Multipliers.id[○].from[Z], ~⚬.id[○]))
  }

  sealed trait Proper[A, AA] extends Multipliers[A, AA] {
    given inputKind: KindN[A]
    given outKind: KindN[AA]

    override def >[BB](that: Multipliers[AA, BB]): Multipliers.Proper[A, BB]

    override def project[BB](
      p: Projection[×, AA, BB],
    ): Exists[[B] =>> (Projection[×, A, B], Multipliers.Proper[B, BB])]

    override def preShuffle[Z](
      s: Z ~⚬ A,
    ): Exists[[ZZ] =>> (Multipliers.Proper[Z, ZZ], ZZ ~⚬ AA)] =
      s.preShuffle(this)
  }

  case class Single[A, AA](value: Multiplier[×, A, AA])(using
    val inKind: Kind[A],
  ) extends Proper[A, AA] {
    override def inputKind: KindN[A] =
      KindN(inKind)

    override def outKind: KindN[AA] =
      value.apply(KindN(inKind))

    override def after[A0](m: Multiplier[×, A0, A])(using Kind[A0]): Multiplier[×, A0, AA] =
      m match
        case Multiplier.Id() => value
        case m: Multiplier.Dup[pr, a, b, c] => Kind.cannotBePair(inKind: Kind[b × c])

    override def >[BB](that: Multipliers[AA, BB]): Proper[A, BB] =
      Single(that after value)

    override def apply[F[_]](fa: F[A])(using StrongZippable[×, F]): F[AA] =
      value.apply(fa)

    private lazy val inputIsAtomic: [x, y] => (A =:= (x × y)) => Nothing =
      [x, y] => (ev: A =:= (x × y)) => Kind.cannotBePair(ev.substituteCo(inKind))

    override def project[BB](
      p: Projection[×, AA, BB],
    ): Exists[[B] =>> (Projection[×, A, B], Proper[B, BB])] =
      val m1 = (value project p)(inputIsAtomic)
      Exists(Projection.id, Single(m1))
  }

  case class Par[A, B, AA, BB](
    m1: Multipliers.Proper[A, AA],
    m2: Multipliers.Proper[B, BB],
  ) extends Multipliers.Proper[A × B, AA × BB] {
    override def inputKind: KindN[A × B] =
      m1.inputKind × m2.inputKind

    override def outKind: KindN[AA × BB] =
      m1.outKind × m2.outKind

    override def after[A0](m: Multiplier[×, A0, A × B])(using Kind[A0]): Multiplier[×, A0, AA × BB] =
      m match
        case Multiplier.Id() => Kind.cannotBePair[A, B](summon[Kind[A0]])
        case Multiplier.Dup(n1, n2) => Multiplier.Dup(m1 after n1, m2 after n2)

    override def >[CC](that: Multipliers[AA × BB, CC]): Multipliers.Proper[A × B, CC] =
      that match
        case Par(n1, n2)   => Par(m1 > n1, m2 > n2)
        case s @ Single(_) => Kind.cannotBePair(s.inKind)

    override def apply[F[_]](fab: F[A × B])(using F: StrongZippable[×, F]): F[AA × BB] =
      val (fa, fb) = F.unzip(fab)
      F.zip(m1(fa), m2(fb))

    override def project[CC](
      p: Projection[×, AA × BB, CC],
    ): Exists[[C] =>> (Projection[×, A × B, C], Multipliers.Proper[C, CC])] =
      p match
        case Projection.Id() =>
          Exists((Projection.Id(), this))
        case Projection.DiscardFst(p2) =>
          UnhandledCase.raise(s"$this.project($p)")
        case Projection.DiscardSnd(p1) =>
          UnhandledCase.raise(s"$this.project($p)")
        case Projection.Fst(p1) =>
          m1.project(p1) match
            case Exists.Some((p1, m1)) =>
              Exists((p1.inFst, Par(m1, m2)))
        case Projection.Snd(p2) =>
          m2.project(p2) match
            case Exists.Some((p2, m2)) =>
              Exists((p2.inSnd, Par(m1, m2)))
        case Projection.Both(p1, p2) =>
          (m1.project(p1), m2.project(p2)) match
            case (Exists.Some((p1, m1)), Exists.Some((p2, m2))) =>
              Exists((Projection.par(p1, p2), Par(m1, m2)))
  }

  def id[A](a: Kind[A]): Multipliers.Proper[A, A] =
    Single(Multiplier.Id())(using a)

  def idProper[A](using a: KindN[A]): Multipliers.Proper[A, A] =
    a.foldMap[[x] =>> Proper[x, x]](
      map = [k] => (k: Kind[k]) => id(k),
      zip = [k, l] => (k: Proper[k, k], l: Proper[l, l]) => Par(k, l),
    )

  def id[A](using a: Kinds[A]): Multipliers[A, A] =
    a.nonEmpty match
      case Left(TypeEq(Refl())) => None
      case Right(a) => idProper(using a)

  def proveId[AA](m: Multipliers[○, AA]): AA =:= ○ =
    m match
      case None => summon
      case p: Proper[a, aa] => KindN.cannotBeUnit(p.inputKind)

  def dup[A](using Kind[A]): Multipliers.Proper[A, A × A] =
    Single(Multiplier.dup)

  def dup[A](a: KindN[A]): Exists[[X] =>> (Multipliers.Proper[A, X], X ~⚬ (A × A))] =
    a match
      case KindN.Type =>
        Exists((dup[●], ~⚬.id))
      case KindN.Prod(k, l) =>
        (dup(k), dup(l)) match
          case (Exists.Some((m1, s1)), Exists.Some((m2, s2))) =>
            Exists((Par(m1, m2), ~⚬.par(s1, s2) > ~⚬.ixi))

  given PairwiseRel[×, ×, Multipliers.Proper] with
    override def pair[A1, A2, B1, B2](
      m1: Multipliers.Proper[A1, B1],
      m2: Multipliers.Proper[A2, B2],
    ): Multipliers.Proper[A1 × A2, B1 × B2] =
      Par(m1, m2)

    override def unpair[A1, A2, B](m: Multipliers.Proper[A1 × A2, B]): Unpaired[A1, A2, B] =
      m match
        case Par(m1, m2)   => Unpaired.Impl(m1, m2)
        case s @ Single(_) => Kind.cannotBePair(s.inKind)
}