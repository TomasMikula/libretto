package libretto.lambda

trait SymmetricSemigroupalCategory[->[_, _], |*|[_, _]] extends SemigroupalCategory[->, |*|] {
  def swap[A, B]: (A |*| B) -> (B |*| A)

  def ix[A, B, C]: ((A |*| B) |*| C) -> ((A |*| C) |*| B) =
    assocLR > par(id, swap) > assocRL

  def xi[A, B, C]: (A |*| (B |*| C)) -> (B |*| (A |*| C)) =
    assocRL > par(swap, id) > assocLR

  def ixi[A, B, C, D]: ((A |*| B) |*| (C |*| D)) -> ((A |*| C) |*| (B |*| D)) =
    assocLR > par(id, assocRL > par(swap, id) > assocLR) > assocRL
}
