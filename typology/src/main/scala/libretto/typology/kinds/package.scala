package libretto.typology

import libretto.lambda.StrongZippable
import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

package object kinds {

  /** Phantom type representing the kind of types. Unicode character U+25CF */
  sealed trait ●

  /** Phantom type representing a pair of kinds. Unicode character U+00D7. */
  sealed trait ×[K, L]
  object × {
    given BiInjective[×] with
      override def unapply[A, B, X, Y](ev: (A × B) =:= (X × Y)): (A =:= X, B =:= Y) =
        ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  /** Phantom type representing the "unit" kind. Neutral element for [[×]]. Unicode character U+25CB. */
  sealed trait ○

  sealed trait Kind[K] {
    def properKind: Either[K =:= ○, ProperKind[K]]

    def testEqual[L](that: Kind[L]): Option[K =:= L] =
      (this, that) match {
        case (Kind.Unit, Kind.Unit) =>
          Some(implicitly[○ =:= ○])
        case (Kind.Type, Kind.Type) =>
          Some(implicitly[● =:= ●])
        case (Kind.Prod(a, b), Kind.Prod(x, y)) =>
          (a.kind testEqual x.kind, b.kind testEqual y.kind) match {
            case (Some(ax), Some(by)) =>
              Some(implicitly[K =:= K].asInstanceOf[K =:= L])
            case _ =>
              None
          }
        case _ =>
          None
      }
  }

  object Kind {
    case object Unit extends Kind[○] {
      override def toString = "○"
      override def properKind = Left(summon[○ =:= ○])
    }
    case object Type extends Kind[●] {
      override def toString = "●"
      override def properKind = Right(ProperKind.Type)
    }
    case class Prod[K, L](k: ProperKind[K], l: ProperKind[L]) extends Kind[K × L] {
      override def toString = s"($k × $l)"
      override def properKind = Right(ProperKind.Prod(k, l))
    }

    given Kind[○] = Unit
    given [K](using k: ProperKind[K]): Kind[K] = k.kind

    def fst[K, L](kl: Kind[K × L]): ProperKind[K] =
      kl match {
        case Prod(k, l) => k
      }

    def snd[K, L](kl: Kind[K × L]): ProperKind[L] =
      kl match {
        case Prod(k, l) => l
      }

    val unitIsNotPair: [x, y] => (○ =:= (x × y)) => Nothing =
      [x, y] => (ev: ○ =:= (x × y)) => {
        val k: ProperKind[○] = ev.substituteContra(ProperKind.fromProd(ev.substituteCo(summon[Kind[○]])))
        ProperKind.cannotBeUnit(k)
      }
  }

  /** Kind not containing the auxiliary unit kind [[○]]. */
  sealed trait ProperKind[K] {
    import ProperKind.*

    def ×[L](l: ProperKind[L]): ProperKind[K × L] =
      ProperKind.Prod(this, l)

    def kind: Kind[K] =
      this match {
        case ProperKind.Type       => Kind.Type
        case ProperKind.Prod(k, l) => Kind.Prod(k, l)
      }

    def foldMap[F[_]](
      map: [k] => OutputKind[k] => F[k],
      zip: [k, l] => (F[k], F[l]) => F[k × l],
    ): F[K] =
      this match
        case Type       => map(OutputKind.Type)
        case Prod(k, l) => zip(k.foldMap(map, zip), l.foldMap(map, zip))

    override def toString: String =
      kind.toString
  }
  object ProperKind {
    def apply[K](using k: ProperKind[K]): ProperKind[K] =
      k

    case object Type extends ProperKind[●]
    case class Prod[K, L](k: ProperKind[K], l: ProperKind[L]) extends ProperKind[K × L]

    given [K, L](using k: ProperKind[K], l: ProperKind[L]): ProperKind[K × L] = Prod(k, l)
    given [K](using k: OutputKind[K]): ProperKind[K] = k.properKind

    def fromProd[K, L](kl: Kind[K × L]): ProperKind[K × L] =
      kl match {
        case Kind.Prod(k, l) => Prod(k, l)
      }

    def unpair[K, L](kl: ProperKind[K × L]): (ProperKind[K], ProperKind[L]) =
      kl match
        case ProperKind.Prod(k, l) => (k, l)

    def unpair[K, L](kl: Kind[K × L]): (ProperKind[K], ProperKind[L]) =
      kl match
        case Kind.Prod(k, l) => (k, l)

    def cannotBeUnit(p: ProperKind[○]): Nothing =
      throw AssertionError("Impossible")

    given StrongZippable[×, ProperKind] with
      override def zip[A, B](a: ProperKind[A], b: ProperKind[B]): ProperKind[A × B] = a × b
      override def unzip[A, B](ab: ProperKind[A × B]): (ProperKind[A], ProperKind[B]) = unpair(ab)
  }

  /** Witnesses that `K` is a legal output kind of type functions. */
  sealed trait OutputKind[K] {
    def kind: Kind[K] =
      this match {
        case OutputKind.Type => Kind.Type
      }

    def properKind: ProperKind[K] =
      this match {
        case OutputKind.Type => ProperKind.Type
      }

    def isNotPair: [x, y] => (K =:= (x × y)) => Nothing =
      [x, y] => (ev: K =:= (x × y)) =>
        OutputKind.cannotBePair(ev.substituteCo(OutputKind.this))

    override def toString: String =
      kind.toString
  }
  object OutputKind {
    case object Type extends OutputKind[●]

    given OutputKind[●] = Type

    def apply[K](using OutputKind[K]): OutputKind[K] =
      summon[OutputKind[K]]

    def cannotBePair[K, L](ab: OutputKind[K × L]): Nothing =
      throw AssertionError("Impossible")
  }
}
