package libretto.cats

/** Witnesses that `F` is a monad in the category `->`. */
trait Monad[->[_, _], F[_]] extends Functor[->, F] {
  def pure[A]    :       A -> F[A]
  def flatten[A] : F[F[A]] -> F[A]

  import category.*

  def liftF[A, B](f: A -> F[B]): F[A] -> F[B] =
    lift(f) > flatten

  extension [A, B](f: A -> F[B]) {
    def >=[C](g: B -> F[C]): A -> F[C] =
      f > liftF(g)
  }
}
