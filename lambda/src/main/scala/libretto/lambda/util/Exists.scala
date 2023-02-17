package libretto.lambda.util

sealed trait Exists[F[_]] {
  type T
  val value: F[T]
}

object Exists {
  case class Some[F[_], A](override val value: F[A]) extends Exists[F] {
    override type T = A
  }

  def apply[F0[_], A](fa: F0[A]): Exists[F0] =
    Some(fa)
}
