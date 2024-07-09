package libretto.lambda.util

/** Equality test where _value_ equality of `a: F[A]`, `b: F[B]` implies type equality `A =:= B`.
 *  I.e., value equality _"clamps"_ `A` and `B` together.
 *
 *  Corollary: a value `a: F[A]` cannot also be assigned a type `F[B]` where `B != A`:
 *  `testEqual(a: F[A], a: F[B])` results in `Some[A =:= B]`.
 */
trait ClampEq[F[_]] {
  def testEqual[A, B](a: F[A], b: F[B]): Option[A =:= B]
}