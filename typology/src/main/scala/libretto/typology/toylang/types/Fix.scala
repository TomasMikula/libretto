package libretto.typology.toylang.types

/** The usual type-level fixed-point. */
case class Fix[F[_]](unfix: F[Fix[F]])
