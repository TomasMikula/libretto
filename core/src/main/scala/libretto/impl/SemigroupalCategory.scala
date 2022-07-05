package libretto.impl

import libretto.Category

trait SemigroupalCategory[->[_, _], |*|[_, _]] extends Category[->] {
  def par[A1, A2, B1, B2](f1: A1 -> B1, f2: A2 -> B2): (A1 |*| A2) -> (B1 |*| B2)

  def assocLR[A, B, C]: ((A |*| B) |*| C) -> (A |*| (B |*| C))
  def assocRL[A, B, C]: (A |*| (B |*| C)) -> ((A |*| B) |*| C)

  def fst[X, Y, Z](f: X -> Y): (X |*| Z) -> (Y |*| Z) = par(f, id)
  def snd[X, Y, Z](f: Y -> Z): (X |*| Y) -> (X |*| Z) = par(id, f)
}
