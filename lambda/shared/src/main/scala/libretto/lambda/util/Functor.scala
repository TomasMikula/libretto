package libretto.lambda.util

trait Functor[F[_]] {

  extension [A](fa: F[A]) {
    infix def map[B](f: A => B): F[B]

    def widen[B >: A]: F[B] =
      map(identity)
  }

}
