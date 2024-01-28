package libretto.typology.toylang.types

import libretto.lambda.{PairwiseRel, Projection, UnhandledCase}
import libretto.lambda.util.{Exists, ExistsCo, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.typology.kinds.*
import libretto.typology.types.kindShuffle.~⚬

sealed trait Multipliers[A, AA] {
  def after[A0](m: Multiplier[×, A0, A])(using OutputKind[A0]): Multiplier[×, A0, AA]

  def >[BB](that: Multipliers[AA, BB]): Multipliers[A, BB]

  def project[BB](
    p: Projection[×, AA, BB],
  ): ExistsCo[[B] =>> (Projection[×, A, B], Multipliers[B, BB])]

  def preShuffle[Z](s: Z ~⚬ A): ExistsCo[[ZZ] =>> (Multipliers[Z, ZZ], ZZ ~⚬ AA)]
}

object Multipliers {
  case object None extends Multipliers[○, ○] {
    override def after[A0](m: Multiplier[×, A0, ○])(using OutputKind[A0]): Multiplier[×, A0, ○] =
      m

    override def >[BB](that: Multipliers[○, BB]): Multipliers[○, BB] =
      that

    override def project[BB](
      p: Projection[×, ○, BB],
    ): Exists[[B] =>> (Projection[×, ○, B], Multipliers[B, BB])] =
      UnhandledCase.raise(s"$this.project($p)")

    override def preShuffle[Z](s: Z ~⚬ ○): ExistsCo[[ZZ] =>> (Multipliers[Z, ZZ], ZZ ~⚬ ○)] =
      UnhandledCase.raise(s"$this.preShuffle($s)")
  }

  sealed trait Proper[A, AA] extends Multipliers[A, AA] {
    def inputKind: ProperKind[A]
    def outKind: ProperKind[AA]

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
    val inKind: OutputKind[A],
  ) extends Proper[A, AA] {
    override def inputKind: ProperKind[A] =
      inKind.properKind

    override def outKind: ProperKind[AA] =
      value.apply(inKind.properKind)

    override def after[A0](m: Multiplier[×, A0, A])(using OutputKind[A0]): Multiplier[×, A0, AA] =
      m match
        case Multiplier.Id() => value
        case m: Multiplier.Dup[pr, a, b, c] => OutputKind.cannotBePair(inKind: OutputKind[b × c])

    override def >[BB](that: Multipliers[AA, BB]): Proper[A, BB] =
      Single(that after value)

    private lazy val inputIsAtomic: [x, y] => (A =:= (x × y)) => Nothing =
      [x, y] => (ev: A =:= (x × y)) => OutputKind.cannotBePair(ev.substituteCo(inKind))

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
    override def inputKind: ProperKind[A × B] =
      m1.inputKind × m2.inputKind

    override def outKind: ProperKind[AA × BB] =
      m1.outKind × m2.outKind

    override def after[A0](m: Multiplier[×, A0, A × B])(using OutputKind[A0]): Multiplier[×, A0, AA × BB] =
      m match
        case Multiplier.Id() => OutputKind.cannotBePair[A, B](summon[OutputKind[A0]])
        case Multiplier.Dup(n1, n2) => Multiplier.Dup(m1 after n1, m2 after n2)

    override def >[CC](that: Multipliers[AA × BB, CC]): Multipliers.Proper[A × B, CC] =
      UnhandledCase.raise(s"$this > $that")

    override def project[CC](
      p: Projection[×, AA × BB, CC],
    ): Exists[[C] =>> (Projection[×, A × B, C], Multipliers.Proper[C, CC])] =
      p match
        case Projection.Id() =>
          Exists((Projection.Id(), this))
        case p =>
          UnhandledCase.raise(s"$this.project($p)")
  }

  def id[A](a: OutputKind[A]): Multipliers.Proper[A, A] =
    Single(Multiplier.Id())(using a)

  def idProper[A](using a: ProperKind[A]): Multipliers.Proper[A, A] =
    a.foldMap[[x] =>> Proper[x, x]](
      map = [k] => (k: OutputKind[k]) => id(k),
      zip = [k, l] => (k: Proper[k, k], l: Proper[l, l]) => Par(k, l),
    )

  def id[A](using a: Kind[A]): Multipliers[A, A] =
    a.properKind match
      case Left(TypeEq(Refl())) => None
      case Right(a) => idProper(using a)

  def proveId[AA](m: Multipliers[○, AA]): AA =:= ○ =
    m match
      case None => summon
      case p: Proper[a, aa] => ProperKind.cannotBeUnit(p.inputKind)

  given PairwiseRel[×, ×, Multipliers.Proper] with
    override def pair[A1, A2, B1, B2](
      m1: Multipliers.Proper[A1, B1],
      m2: Multipliers.Proper[A2, B2],
    ): Multipliers.Proper[A1 × A2, B1 × B2] =
      Par(m1, m2)

    override def unpair[A1, A2, B](m: Multipliers.Proper[A1 × A2, B]): Unpaired[A1, A2, B] =
      m match
        case Par(m1, m2)   => Unpaired.Impl(m1, m2)
        case s @ Single(_) => OutputKind.cannotBePair(s.inKind)
}