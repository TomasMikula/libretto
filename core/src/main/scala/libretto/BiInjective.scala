package libretto

trait BiInjective[F[_, _]] {
  def unapply[A, B, X, Y](ev: F[A, B] =:= F[X, Y]): (A =:= X, B =:= Y)
}
