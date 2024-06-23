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

/** A domain-level `Either`.
  *
  * Uninhabited, used only as a (phantom) type index.
  */
sealed trait ++[A, B]

given BiInjective[++] with {
  override def unapply[A, B, X, Y](ev: A ++ B =:= X ++ Y): (A =:= X, B =:= Y) =
    ev match { case TypeEq(Refl()) => (summon, summon) }
}

/** References an external input port. */
sealed trait PortName[A]

/** Value `A` to be read from an external input port */
sealed trait Reading[A]
