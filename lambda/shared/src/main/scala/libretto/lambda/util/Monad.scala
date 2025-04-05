package libretto.lambda.util

import scala.concurrent.{ExecutionContext, Future}
import scala.annotation.targetName

/** Witnesses that `F` is a monad in the category of Scala functions. */
trait Monad[F[_]] extends Functor[F] {
  def pure[A](a: A): F[A]

  extension [A](fa: F[A]) {
    infix def flatMap[B](f: A => F[B]): F[B]

    override infix def map[B](f: A => B): F[B] =
      flatMap(a => pure(f(a)))

    infix def *>[B](fb: F[B]): F[B] =
      flatMap(_ => fb)

    infix def >>[B](fb: => F[B]): F[B] =
      flatMap(_ => fb)

    def void: F[Unit] =
      map(_ => ())
  }

  /** An [[Applicative]] derived from this Monad instance.
   *
   * Note that it is intentional that
   *  - Monad is not made to `extend` Applicative.
   *  - The Applicative derived from this Monad (i.e. this field) is not `given`.
   * The reason is that we often want to use a different Applicative instance by default.
   */
  lazy val applicative: Applicative[F] =
    Monad.deriveApplicative(using this)

  extension [A](ffa: F[F[A]]) {
    def flatten: F[A] =
      flatMap(ffa)(identity)
  }
}

object Monad {
  def apply[F[_]](using Monad[F]): Monad[F] =
    summon

  def deriveApplicative[F[_]](using F: Monad[F]): Applicative[F] =
    new Applicative[F] {
      override def pure[A](a: A): F[A] =
        F.pure(a)

      extension [A](fa: F[A]) {
        override def map[B](f: A => B): F[B] =
          F.map(fa)(f)

        override def zip[B](fb: F[B]): F[(A, B)] =
          F.flatMap(fa) { a => F.map(fb)((a, _)) }
      }
    }

  given monadId: Monad[[A] =>> A] with {
    override def pure[A](a: A): A =
      a

    extension [A](a: A)
      override def flatMap[B](f: A => B): B =
        f(a)
  }

  given monadEither[E]: Monad[[A] =>> Either[E, A]] with {
    override def pure[A](a: A): Either[E, A] =
      Right(a)

    extension [A](fa: Either[E, A])
      override def flatMap[B](f: A => Either[E, B]): Either[E, B] =
        fa.flatMap(f)
  }

  given monadFuture(using ec: ExecutionContext): Monad[Future] with {
      override def pure[A](a: A): Future[A] =
        Future.successful(a)

      extension [A](fa: Future[A])
        override def flatMap[B](f: A => Future[B]): Future[B] =
          fa.flatMap(f)(using ec)
    }
}
