package libretto.impl

trait Unique[F[_]] {
  def testEqual[A, B](a: F[A], b: F[B]): Option[A =:= B]
}