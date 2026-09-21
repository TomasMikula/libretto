package libretto.lambda

import libretto.lambda.util.Exists

/** Witnesses that any types `A`, `B` satisfying the "property" `F`
  * induce a third type `R` such that `Rel[A, B, R]`.
  *
  * When seeing `Rel` as a binary operation relating the two inputs to output,
  * we can say that the set of `F`-constrained types "supports" the operation `Rel`.
  */
infix trait Supports2[F[_], Rel[_, _, _]] {
  def apply[A, B](a: F[A], b: F[B]): Exists[[R] =>> Rel[A, B, R]]
}
