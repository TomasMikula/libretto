package libretto.lambda.examples.workflow.generic.lang

import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** A domain-level pair.
  *
  * Uninhabited, used only as a (phantom) type index.
  */
sealed trait **[A, B]

given BiInjective[**] with {
  override def unapply[A, B, X, Y](ev: A ** B =:= X ** Y): (A =:= X, B =:= Y) =
    ev match { case TypeEq(Refl()) => (summon, summon) }
}

/** Used for declaring members of an ADT. */
sealed trait ::[Name, Type]

given BiInjective[::] with {
  override def unapply[A, B, X, Y](ev: A :: B =:= X :: Y): (A =:= X, B =:= Y) =
    ev match { case TypeEq(Refl()) => (summon, summon) }
}

/** Used as a separator of members of an ADT. */
sealed trait ||[A, B]

given BiInjective[||] with {
  override def unapply[A, B, X, Y](ev: (A || B) =:= (X || Y)): (A =:= X, B =:= Y) =
    ev match { case TypeEq(Refl()) => (summon, summon) }
}

/** Domain-level user-definable sum type. */
sealed trait Enum[Cases]

/** Domain-level `Either`. */
type ++[A, B] = Enum["Left" :: A || "Right" :: B]

given BiInjective[++] with {
  override def unapply[A, B, X, Y](ev: A ++ B =:= X ++ Y): (A =:= X, B =:= Y) =
    ev match { case TypeEq(Refl()) => (summon, summon) }
}

/** Domain-level string. */
sealed trait Str

/** References an external input port. */
sealed trait PortName[A]

/** Value `A` to be read from an external input port */
sealed trait Reading[A]
