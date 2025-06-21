package libretto.lambda.util

sealed trait ExistsCo[+F[_]] {
  type T
  val value: F[T]
}

sealed trait Exists[F[_]] extends ExistsCo[F]

object Exists {
  case class Indeed[F[_], A](override val value: F[A]) extends Exists[F] {
    override type T = A
  }

  def apply[F0[_], A](fa: F0[A]): Exists[F0] =
    Indeed(fa)
}

sealed trait ExistsK[F[_[_]]] {
  type T[_]
  val value: F[T]
}

object ExistsK {
  case class Indeed[F[_[_]], A[_]](override val value: F[A]) extends ExistsK[F] {
    override type T[X] = A[X]
  }

  def apply[F0[_[_]], A[_]](fa: F0[A]): ExistsK[F0] =
    Indeed(fa)
}