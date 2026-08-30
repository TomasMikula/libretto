package libretto.lambda

trait SemigroupalCategory[->[_, _], |*|[_, _]]
  extends NarrowSemigroupalCategory[[x] =>> Unit, ->, |*|]
  with Category[->]
{
  def assocLR[A, B, C]: ((A |*| B) |*| C) -> (A |*| (B |*| C))

  def assocRL[A, B, C]: (A |*| (B |*| C)) -> ((A |*| B) |*| C)

  def fst[X, Y, Z](f: X -> Y): (X |*| Z) -> (Y |*| Z) = par(f, id)

  def snd[X, Y, Z](f: Y -> Z): (X |*| Y) -> (X |*| Z) = par(id, f)

  override def tensor[A, B](wa: Unit, wb: Unit): Unit = ()
  override def assocLR[A, B, C](a: Unit, b: Unit, c: Unit): ((A |*| B) |*| C) -> (A |*| (B |*| C)) = assocLR[A, B, C]
  override def assocRL[A, B, C](a: Unit, b: Unit, c: Unit): (A |*| (B |*| C)) -> ((A |*| B) |*| C) = assocRL[A, B, C]
  override def fst[X, Y, Z](f: X -> Y, z: Unit): (X |*| Z) -> (Y |*| Z) = fst(f)
  override def snd[X, Y, Z](x: Unit, f: Y -> Z): (X |*| Y) -> (X |*| Z) = snd(f)

  extension [A, B](f: A -> B) {
    def inFst[X]: (A |*| X) -> (B |*| X) = fst(f)
    def inSnd[X]: (X |*| A) -> (X |*| B) = snd(f)

    def at[F[_]](pos: Focus[|*|, F]): F[A] -> F[B] =
      pos match
        case Focus.Id()    => f
        case Focus.Fst(p1) => fst(f.at(p1))
        case Focus.Snd(p2) => snd(f.at(p2))
  }
}
