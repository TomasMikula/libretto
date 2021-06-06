package libretto.impl

trait SymmetricSemigroupalCategory[->[_, _], |*|[_, _]] extends SemigroupalCategory[->, |*|] {
  def swap[A, B]: (A |*| B) -> (B |*| A)
}
