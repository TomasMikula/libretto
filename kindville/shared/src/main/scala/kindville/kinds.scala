package kindville

sealed trait *
sealed trait ->[K, L]

sealed trait ::[H <: AnyKind, T]
sealed trait TNil

infix sealed trait ofKind[F <: AnyKind, K]

object ofKind {

  given [A] => (A ofKind *) =
    new (A ofKind *) {}

  given [F[_]] => (F ofKind (* -> *)) =
    new (F ofKind (* -> *)) {}

  given [F2[_, _]] => (F2 ofKind ((* :: * :: TNil) -> *)) =
    new (F2 ofKind ((* :: * :: TNil) -> *)) {}

  given [H[_[_]]] => (H ofKind ((* -> *) -> *)) =
    new (H ofKind ((* -> *) -> *)) {}

  given [HA[_, _[_]]] => (HA ofKind ((* :: (* -> *) :: TNil) -> *)) =
    new (HA ofKind ((* :: (* -> *) :: TNil) -> *)) {}

  // TODO: provide macro-generated evidence for arbitrary kinds
}

infix sealed trait ofMultiKind[As, Ks]

object ofMultiKind {

  given (TNil ofMultiKind TNil) =
    new (TNil ofMultiKind TNil) {}

  given [A0 <: AnyKind, As, K0, Ks] => (A0 ofKind K0, As ofMultiKind Ks) => ((A0 :: As) ofMultiKind (K0 :: Ks)) =
    new ((A0 :: As) ofMultiKind (K0 :: Ks)) {}

}

infix sealed trait ofKinds[As <: AnyKind, Ks]

object ofKinds {

  given [A <: AnyKind, K] => (A ofKind K) => (A ofKinds K) =
    new (A ofKinds K) {}

  given [As, Ks] => (As ofMultiKind Ks) => (As ofKinds Ks) =
    new (As ofKinds Ks) {}

}

private[kindville] sealed trait Kind:
  type Label

  def show: String

private[kindville] object Kind:
  type Of[K] = Kind { type Label = K }

  case object Tp extends Kind {
    override type Label = *

    override def show: String = "*"
  }

  case class Arr[Ks, L](
    paramKinds: Kinds.Of[Ks],
    outKind: Kind.Of[L],
  ) extends Kind {
    override type Label = Ks -> L

    override def show: String =
      paramKinds.show + " -> " + outKind.show
  }

  def arr(ks: Kinds, l: Kind): Kind.Of[ks.Label -> l.Label] =
    Arr(ks, l)

private[kindville] sealed trait Kinds:
  type Label

  def ::(k: Kind): Kinds.Of[k.Label :: Label] =
    Kinds.Cons(k, this)

  def toList: List[Kind] =
    this match
      case Kinds.Empty      => Nil
      case Kinds.Cons(h, t) => h :: t.toList

  def show: String =
    toList.map(_.show).appended("TNil").mkString("(", " :: ", ")")

private[kindville] object Kinds:
  type Of[Ks] = Kinds { type Label = Ks }

  case object Empty extends Kinds {
    override type Label = TNil
  }

  case class Cons[K, Ks](
    head: Kind.Of[K],
    tail: Kinds.Of[Ks],
  ) extends Kinds {
    override type Label = K :: Ks
  }

  def single(k: Kind): Kinds.Of[k.Label :: TNil] =
    Cons(k, Kinds.Empty)
