package kindville.util

trait Applicative[F[_]] {
  def pure[A](a: A): F[A]

  extension [A](fa: F[A]) {
    def map[B](f: A => B): F[B]
    infix def zip[B](fb: F[B]): F[(A, B)]
  }

  extension [A](as: List[A]) {
    def traverseList[B](f: A => F[B]): F[List[B]] =
      as match
        case Nil => pure(Nil)
        case h :: t => (f(h) zip t.traverseList(f)).map { case (h, t) => h :: t }
  }
}

object Applicative {
  given [L] => Applicative[Either[L, _]] =
    new Applicative[Either[L, _]] {
      override def pure[A](a: A): Either[L, A] = Right(a)

      extension [A](fa: Either[L, A]) {
        override def map[B](f: A => B): Either[L, B] = fa.map(f)
        override def zip[B](fb: Either[L, B]): Either[L, (A, B)] = fa.flatMap(a => fb.map((a, _)))
      }
    }
}
