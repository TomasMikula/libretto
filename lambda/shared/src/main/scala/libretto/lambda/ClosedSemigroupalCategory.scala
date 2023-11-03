package libretto.lambda

trait ClosedSemigroupalCategory[->[_, _], |*|[_, _], -->[_, _]] extends SemigroupalCategory[->, |*|] {
  def curry[A, B, C](f: (A |*| B) -> C): A -> (B --> C)

  def eval[A, B]: ((A --> B) |*| A) -> B

  def uncurry[A, B, C](f: A -> (B --> C)): (A |*| B) -> C =
    andThen(fst(f), eval)
}
