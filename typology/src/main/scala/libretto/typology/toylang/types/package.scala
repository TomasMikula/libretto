package libretto.typology.toylang.types

/** Used as a phantom type representing a reference to a surrounding recursive function. */
sealed trait RecCall[A, B]

/** Used as a phantom type representing the usual type-level fixed-point. */
sealed trait Fix[F[_]]
