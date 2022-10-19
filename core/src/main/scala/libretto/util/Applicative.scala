package libretto.util

trait Applicative[F[_]] {
  def ap[A, B](ff: F[A => B])(fa: F[A]): F[B]
  def pure[A](a: A): F[A]

  def map[A, B](fa: F[A])(f: A => B): F[B] =
    ap(pure(f))(fa)

  def map2[A, B, R](fa: F[A], fb: F[B])(f: (A, B) => R): F[R] =
    ap(map(fa)(a => f(a, _)))(fb)

  def mapN[A, B, C, R](fa: F[A], fb: F[B], fc: F[C])(f: (A, B, C) => R): F[R] =
    map2(fa, map2(fb, fc)((b, c) => (a: A) => f(a, b, c)))((a, g) => g(a))
}