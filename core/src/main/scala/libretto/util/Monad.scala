package libretto.util

import scala.concurrent.{ExecutionContext, Future}

trait Monad[F[_]] {
  def flatMap[A, B](fa: F[A], f: A => F[B]): F[B]

  def pure[A](a: A): F[A]

  def map[A, B](fa: F[A], f: A => B): F[B] =
    flatMap(fa, a => pure(f(a)))
}

object Monad {
  object syntax {
    extension [F[_], A](fa: F[A])(using F: Monad[F]) {
      def map[B](f: A => B): F[B] =
        F.map(fa, f)

      def flatMap[B](f: A => F[B]): F[B] =
        F.flatMap(fa, f)
    }
  }

  given monadFuture(using ec: ExecutionContext): Monad[Future] with {
      override def pure[A](a: A): Future[A] =
        Future.successful(a)

      override def flatMap[A, B](fa: Future[A], f: A => Future[B]): Future[B] =
        fa.flatMap(f)(using ec)
    }
}
