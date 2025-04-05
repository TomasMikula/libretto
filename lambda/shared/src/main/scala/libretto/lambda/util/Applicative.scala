package libretto.lambda.util

import scala.annotation.targetName

trait Applicative[F[_]] extends Functor[F] {
  def pure[A](a: A): F[A]

  extension [A](fa: F[A]) {
    infix def zip[B](fb: F[B]): F[(A, B)]

    infix def zipWith[B, C](fb: F[B])(f: (A, B) => C): F[C] =
      (fa zip fb) map { case (a, b) => f(a, b) }
  }

  def map2[A, B, R](fa: F[A], fb: F[B])(f: (A, B) => R): F[R] =
    (fa zipWith fb)(f)

  def mapN[A, B, C, R](fa: F[A], fb: F[B], fc: F[C])(f: (A, B, C) => R): F[R] =
    map2(fa, map2(fb, fc)((b, c) => (a: A) => f(a, b, c)))((a, g) => g(a))
}

object Applicative {
  def apply[F[_]](using Applicative[F]): Applicative[F] =
    summon

  extension [A](a: A) {
    def pure[F[_]](using F: Applicative[F]): F[A] =
      F.pure(a)
  }

  def traverseList[A, F[_], B](as: List[A])(f: A => F[B])(using F: Applicative[F]): F[List[B]] =
    as match
      case Nil     => F.pure(Nil)
      case a :: as => F.map2(f(a), traverseList(as)(f))(_ :: _)

  given applicativeId: Applicative[[A] =>> A] with {
    override def pure[A](a: A): A = a

    extension [A](a: A) {
      override def map[B](f: A => B): B = f(a)
      override def zip[B](b: B): (A, B) = (a, b)
      override def widen[B >: A]: B = a
    }
  }

  given applicativeFunction0: Applicative[Function0] with {
    override def pure[A](a: A): () => A = () => a

    extension [A](fa: () => A) {
      override def map[B](f: A => B): () => B = () => f(fa())
      override def zip[B](fb: () => B): () => (A, B) = () => (fa(), fb())
      override def widen[B >: A]: () => B = fa
    }
  }

  given Applicative[Option] with {

    override def pure[A](a: A): Option[A] =
      Some(a)

    extension [A](fa: Option[A]) {
      override def map[B](f: A => B): Option[B] = fa.map(f)

      override def zip[B](fb: Option[B]): Option[(A, B)] =
        (fa, fb) match
          case (Some(a), Some(b)) => Some((a, b))
          case _                  => None

      override def widen[B >: A]: Option[B] = fa
    }
  }
}
