package libretto.typology.kinds

import libretto.lambda.StrongZippable
import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.Refl

/** Evidence that `K` represents one or more kinds (not containing the auxiliary unit kind [[○]]). */
sealed trait KindN[K] {
  import KindN.*

  def ×[L](l: KindN[L]): KindN[K × L] =
    KindN.Prod(this, l)

  def foldMap[F[_]](
    map: [k] => Kind[k] => F[k],
    zip: [k, l] => (F[k], F[l]) => F[k × l],
  ): F[K] =
    this match
      case Type       => map(Kind.Type)
      case Prod(k, l) => zip(k.foldMap(map, zip), l.foldMap(map, zip))

  override def toString: String =
    this match
      case Type       => "●"
      case Prod(k, l) => s"($k × $l)"

  infix def testEqual[L](that: KindN[L]): Option[K =:= L] =
    (this, that) match
      case (KindN.Type, KindN.Type) =>
        Some(implicitly[● =:= ●])
      case (KindN.Prod(a, b), KindN.Prod(x, y)) =>
        (a testEqual x, b testEqual y) match {
          case (Some(TypeEq(Refl())), Some(TypeEq(Refl()))) =>
            Some(implicitly[K =:= L])
          case _ =>
            None
        }
      case _ =>
        None
}

object KindN {
  def apply[K](using k: KindN[K]): KindN[K] =
    k

  case object Type extends KindN[●]
  case class Prod[K, L](k: KindN[K], l: KindN[L]) extends KindN[K × L]

  def apply[K](k: Kind[K]): KindN[K] =
    k match {
      case Kind.Type => KindN.Type
    }

  given [K, L](using k: KindN[K], l: KindN[L]): KindN[K × L] = Prod(k, l)
  given [K](using k: Kind[K]): KindN[K] = KindN(k)

  def unpair[K, L](kl: KindN[K × L]): (KindN[K], KindN[L]) =
    kl match
      case KindN.Prod(k, l) => (k, l)

  def cannotBeUnit(p: KindN[○]): Nothing =
    throw AssertionError("Impossible")

  given StrongZippable[×, KindN] with
    override def zip[A, B](a: KindN[A], b: KindN[B]): KindN[A × B] = a × b
    override def unzip[A, B](ab: KindN[A × B]): (KindN[A], KindN[B]) = unpair(ab)
}
