package libretto.lambda.util

import scala.concurrent.{ExecutionContext, Future}

/** Witnesses that `F` is a monad in the category of Scala functions. */
trait Monad[F[_]] extends Applicative[F] {
  def flatMap[A, B](fa: F[A])(f: A => F[B]): F[B]

  def pure[A](a: A): F[A]

  override def map[A, B](fa: F[A], f: A => B): F[B] =
    flatMap(fa)(a => pure(f(a)))

  override def ap[A, B](ff: F[A => B])(fa: F[A]): F[B] =
    flatMap(ff) { f => map(fa)(f) }

  def flatten[A](a: F[F[A]]): F[A] =
    flatMap(a)(identity)

  def flatMap2[A, B, C](fa: F[A], fb: F[B])(f: (A, B) => F[C]): F[C] =
    flatten(map2(fa, fb)(f))
}

object Monad {
  def apply[F[_]](using Monad[F]): Monad[F] =
    summon

  object syntax {
    extension [F[_], A](fa: F[A])(using F: Monad[F]) {
      def map[B](f: A => B): F[B] =
        F.map(fa, f)

      def flatMap[B](f: A => F[B]): F[B] =
        F.flatMap(fa)(f)

      def *>[B](fb: F[B]): F[B] =
        flatMap(_ => fb)

      def >>[B](fb: => F[B]): F[B] =
        flatMap(_ => fb)

      def void: F[Unit] =
        map(_ => ())
    }
  }

  given monadId: Monad[[A] =>> A] with {
    override def pure[A](a: A): A =
      a

    override def flatMap[A, B](a: A)(f: A => B): B =
      f(a)
  }

  given monadEither[E]: Monad[[A] =>> Either[E, A]] with {
    override def pure[A](a: A): Either[E, A] =
      Right(a)

    override def flatMap[A, B](fa: Either[E, A])(f: A => Either[E, B]): Either[E, B] =
      fa.flatMap(f)
  }

  given monadFuture(using ec: ExecutionContext): Monad[Future] with {
      override def pure[A](a: A): Future[A] =
        Future.successful(a)

      override def flatMap[A, B](fa: Future[A])(f: A => Future[B]): Future[B] =
        fa.flatMap(f)(using ec)
    }
}
