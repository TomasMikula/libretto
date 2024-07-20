package libretto.cats

/** Witnesses that `F` is a comonad in the category `->`. */
trait Comonad[->[_, _], F[_]] extends Functor[->, F] {
  def extract[A]   : F[A] -> A
  def duplicate[A] : F[A] -> F[F[A]]
}
