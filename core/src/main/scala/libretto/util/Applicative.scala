package libretto.util

import scala.annotation.targetName

trait Applicative[F[_]] extends Zippable[Tuple2, F] { self =>
  def ap[A, B](ff: F[A => B])(fa: F[A]): F[B]
  def pure[A](a: A): F[A]

  def map[A, B](fa: F[A], f: A => B): F[B] =
    ap(pure(f))(fa)

  def map2[A, B, R](fa: F[A], fb: F[B])(f: (A, B) => R): F[R] =
    ap(map(fa, a => f(a, _)))(fb)

  def mapN[A, B, C, R](fa: F[A], fb: F[B], fc: F[C])(f: (A, B, C) => R): F[R] =
    map2(fa, map2(fb, fc)((b, c) => (a: A) => f(a, b, c)))((a, g) => g(a))

  def zip[A, B](fa: F[A], fb: F[B]): F[(A, B)] =
    map2(fa, fb)((_, _))

  extension [A](fa: F[A]) {
    @targetName("extMap")
    def map[B](f: A => B): F[B] =
      self.map(fa, f)
  }
}

object Applicative {
  def apply[F[_]](using Applicative[F]): Applicative[F] =
    summon
}
