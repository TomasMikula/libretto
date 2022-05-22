package libretto

/** Witnesses that `F` is a monad in the category `->`. */
trait Monad[->[_, _], F[_]] extends Functor[->, F] {
  def pure[A]    :       A -> F[A]
  def flatten[A] : F[F[A]] -> F[A]
}
