package libretto.lambda.util

import scala.annotation.targetName

trait Applicative[F[_]] { self =>
  def pure[A](a: A): F[A]

  def map[A, B](fa: F[A], f: A => B): F[B]

  def zip[A, B](fa: F[A], fb: F[B]): F[(A, B)]

  def map2[A, B, R](fa: F[A], fb: F[B])(f: (A, B) => R): F[R] =
    map(zip(fa, fb), { case (a, b) => f(a, b) })

  def mapN[A, B, C, R](fa: F[A], fb: F[B], fc: F[C])(f: (A, B, C) => R): F[R] =
    map2(fa, map2(fb, fc)((b, c) => (a: A) => f(a, b, c)))((a, g) => g(a))

  extension [A](fa: F[A]) {
    @targetName("extMap")
    infix def map[B](f: A => B): F[B] =
      self.map(fa, f)

    @targetName("extZip")
    infix def zip[B](fb: F[B]): F[(A, B)] =
      self.zip(fa, fb)

    infix def zipWith[B, C](fb: F[B])(f: (A, B) => C): F[C] =
      self.map2(fa, fb)(f)

    def widen[B >: A]: F[B] =
      map(identity)
  }
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
    override def map[A, B](a: A, f: A => B): B = f(a)
    override def zip[A, B](a: A, b: B): (A, B) = (a, b)

    extension [A](a: A) {
      override def widen[B >: A]: B = a
    }
  }

  given applicativeFunction0: Applicative[Function0] with {
    override def pure[A](a: A): () => A = () => a
    override def map[A, B](fa: () => A, f: A => B): () => B = () => f(fa())
    override def zip[A, B](fa: () => A, fb: () => B): () => (A, B) = () => (fa(), fb())

    extension [A](fa: () => A) {
      override def widen[B >: A]: () => B = fa
    }
  }

  given Applicative[Option] with {
    override def map[A, B](fa: Option[A], f: A => B): Option[B] =
      fa.map(f)

    override def pure[A](a: A): Option[A] =
      Some(a)

    override def zip[A, B](fa: Option[A], fb: Option[B]): Option[(A, B)] =
      (fa, fb) match
        case (Some(a), Some(b)) => Some((a, b))
        case _                  => None

    extension [A](fa: Option[A]) {
      override def widen[B >: A]: Option[B] = fa
    }
  }
}
