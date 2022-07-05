package libretto.util

/** Witnesses that a value `a: F[A]` cannot also be assigned a type `F[B]` where `B != A`. */
trait UniqueTypeArg[F[_]] {
  def testEqual[A, B](a: F[A], b: F[B]): Option[A =:= B]
}