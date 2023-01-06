package libretto.lambda

trait Cartesian[|*|[_, _], F[_]] {
  def zip[A, B](fa: F[A], fb: F[B]): F[A |*| B]
  def unzip[A, B](fab: F[A |*| B]): (F[A], F[B])
}
