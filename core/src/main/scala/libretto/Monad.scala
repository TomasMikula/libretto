package libretto

/** Witnesses that `F` is a monad in the category `->`. */
trait Monad[->[_, _], F[_]](using category: Category[->]) extends Functor[->, F] {
  def pure[A]    :       A -> F[A]
  def flatten[A] : F[F[A]] -> F[A]

  extension [A, B](f: A -> F[B]) {
    def >=[C](g: B -> F[C]): A -> F[C] =
      f > lift(g) > flatten
  }
}
