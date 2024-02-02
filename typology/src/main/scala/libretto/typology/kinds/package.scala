package libretto.typology.kinds

import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

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
