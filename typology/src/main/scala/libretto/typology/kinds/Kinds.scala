package libretto.typology.kinds

import libretto.lambda.{Preserves2, Supports2}
import libretto.lambda.util.Exists

/** Evidence that `K` represents zero or more kinds. */
sealed trait Kinds[K] {
  def nonEmpty: Either[K =:= ○, KindN[K]]

  override def toString: String =
    this match
      case Kinds.Empty       => "○"
      case Kinds.NonEmpty(k) => k.toString

  def testEqual[L](that: Kinds[L]): Option[K =:= L] =
    (this, that) match {
      case (Kinds.Empty, Kinds.Empty) =>
        Some(implicitly[○ =:= ○])
      case (Kinds.NonEmpty(k), Kinds.NonEmpty(l)) =>
        k testEqual l
      case _ =>
        None
    }
}

object Kinds {
  case object Empty extends Kinds[○] {
    override def nonEmpty = Left(summon[○ =:= ○])
  }

  case class NonEmpty[K](value: KindN[K]) extends Kinds[K] {
    override def nonEmpty: Either[K =:= ○, KindN[K]] = Right(value)
  }

  def apply[K](using k: Kinds[K]): Kinds[K] =
    k

  def apply[K](k: Kind[K]): Kinds[K] =
    k match {
      case Kind.Type => NonEmpty(KindN.Type)
    }

  def apply[K](k: KindN[K]): Kinds[K] =
    NonEmpty(k)

  given Kinds[○] = Empty
  given [K](using k: KindN[K]): Kinds[K] = Kinds(k)

  def nonEmpty[K, L](kl: Kinds[K × L]): KindN[K × L] =
    kl match
      case NonEmpty(kl) => kl

  def unpair[K, L](kl: Kinds[K × L]): (KindN[K], KindN[L]) =
    kl match
      case NonEmpty(kl) => KindN.unpair(kl)

  def fstOf[K, L](kl: Kinds[K × L]): KindN[K] =
    unpair(kl)._1

  def sndOf[K, L](kl: Kinds[K × L]): KindN[L] =
    unpair(kl)._2

  val unitIsNotPair: [x, y] => (○ =:= (x × y)) => Nothing =
    [x, y] => (ev: ○ =:= (x × y)) => {
      val k: KindN[○] = ev.substituteContra(nonEmpty(ev.substituteCo(summon[Kinds[○]])))
      KindN.cannotBeUnit(k)
    }

  /** Witness that `P` is the product of kinds `A` and `B` (accounting for absorbing the unit `○`). */
  sealed trait Prod[A, B, P] {
    import Prod.*

    def inKinds1: Kinds[A] =
      this match
        case UnitUnit => Kinds.Empty
        case LeftUnit(_) => Kinds.Empty
        case RightUnit(k) => Kinds(k)
        case Both(k, _) => Kinds(k)

    def inKinds2: Kinds[B] =
      this match
        case UnitUnit => Kinds.Empty
        case LeftUnit(l) => Kinds(l)
        case RightUnit(_) => Kinds.Empty
        case Both(_, l) => Kinds(l)

    def outKinds: Kinds[P] =
      this match
        case UnitUnit => Kinds.Empty
        case LeftUnit(l) => Kinds(l)
        case RightUnit(k) => Kinds(k)
        case Both(k, l) => Kinds(k × l)

    infix def deriveEq[Q](that: Prod[A, B, Q]): P =:= Q
  }

  object Prod {
    case object UnitUnit extends Prod[○, ○, ○]:
      override def deriveEq[Q](that: Prod[○, ○, Q]): ○ =:= Q =
        that match
          case UnitUnit => summon[○ =:= ○]

    case class LeftUnit[L](l: KindN[L]) extends Prod[○, L, L]:
      override def deriveEq[Q](that: Prod[○, L, Q]): L =:= Q =
        that match
          case LeftUnit(_) => summon[L =:= Q]
          case UnitUnit => KindN.cannotBeUnit(summon[L =:= ○].substituteCo(l))

    case class RightUnit[K](k: KindN[K]) extends Prod[K, ○, K]:
      override def deriveEq[Q](that: Prod[K, ○, Q]): K =:= Q =
        that match
          case RightUnit(_) => summon[K =:= Q]
          case UnitUnit => KindN.cannotBeUnit(summon[K =:= ○].substituteCo(k))

    case class Both[K, L](k: KindN[K], l: KindN[L]) extends Prod[K, L, K × L]:
      override def deriveEq[Q](that: Prod[K, L, Q]): (K × L) =:= Q =
        that match
          case Both(_, _) => summon[(K × L) =:= Q]
          case UnitUnit => KindN.cannotBeUnit(summon[K =:= ○].substituteCo(k))
          case LeftUnit(_) => KindN.cannotBeUnit(summon[K =:= ○].substituteCo(k))
          case RightUnit(_) => KindN.cannotBeUnit(summon[L =:= ○].substituteCo(l))


    def apply[A, B](a: Kinds[A], b: Kinds[B]): Exists[[P] =>> Prod[A, B, P]] =
      (a, b) match {
        case (Empty, Empty)             => Exists.Indeed(UnitUnit)
        case (Empty, NonEmpty(l))       => Exists.Indeed(LeftUnit(l))
        case (NonEmpty(k), Empty)       => Exists.Indeed(RightUnit(k))
        case (NonEmpty(k), NonEmpty(l)) => Exists.Indeed(Both(k, l))
      }

    def leftUnit[B](b: Kinds[B]): Prod[○, B, B] =
      b match
        case Empty => UnitUnit
        case NonEmpty(b) => LeftUnit(b)

    def rightUnit[A](a: Kinds[A]): Prod[A, ○, A] =
      a match
        case Empty => UnitUnit
        case NonEmpty(a) => RightUnit(a)

    extension [A, B](k: Kinds.Prod[A, B, ○]) {
      def proveUnitInputs: (A =:= ○, B =:= ○) =
        k match
          case UnitUnit => (summon, summon)
    }
  }

  given (Kinds Supports2 Prod) with {
    override def apply[A, B](
      a: Kinds[A],
      b: Kinds[B],
    ): Exists[[P] =>> Prod[A, B, P]] =
      Prod(a, b)
  }

  given (Prod Preserves2 Kinds) with {
    override def apply[A: Kinds, B: Kinds, C](rel: Prod[A, B, C]): Kinds[C] =
      rel.outKinds
  }
}
