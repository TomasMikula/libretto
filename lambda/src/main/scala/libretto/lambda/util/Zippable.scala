package libretto.lambda.util

trait Zippable[|*|[_, _], F[_]] {
  def zip[A, B](fa: F[A], fb: F[B]): F[A |*| B]
}
