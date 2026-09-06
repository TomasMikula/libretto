package libretto.lambda

import libretto.lambda.util.Applicative

trait SymmetricSemigroupalCategory[->[_, _], |*|[_, _]]
  extends NarrowSymmetricSemigroupalCategory[[x] =>> Unit, ->, |*|]
  with SemigroupalCategory[->, |*|]
{
  def swap[A, B]: (A |*| B) -> (B |*| A)

  def ix[A, B, C]: ((A |*| B) |*| C) -> ((A |*| C) |*| B) =
    assocLR > par(id, swap) > assocRL

  def xi[A, B, C]: (A |*| (B |*| C)) -> (B |*| (A |*| C)) =
    assocRL > par(swap, id) > assocLR

  def ixi[A, B, C, D]: ((A |*| B) |*| (C |*| D)) -> ((A |*| C) |*| (B |*| D)) =
    assocLR > par(id, assocRL > par(swap, id) > assocLR) > assocRL

  override def swap[A, B](using Unit, Unit): (A |*| B) -> (B |*| A) = swap[A, B]
  override def ix[A, B, C](using Unit, Unit, Unit): ((A |*| B) |*| C) -> ((A |*| C) |*| B) = ix[A, B, C]
  override def xi[A, B, C](using Unit, Unit, Unit): (A |*| (B |*| C)) -> (B |*| (A |*| C)) = xi[A, B, C]
  override def ixi[A, B, C, D](using Unit, Unit, Unit, Unit): ((A |*| B) |*| (C |*| D)) -> ((A |*| C) |*| (B |*| D)) = ixi[A, B, C, D]

  def hoist[G[_]](using Applicative[G]): SymmetricSemigroupalCategory[[a, b] =>> G[a -> b], |*|] =
    new SymmetricSemigroupalCategory.Hoisted[G, ->, |*|] {
      override val applicative: Applicative[G] = summon
      override val base: SymmetricSemigroupalCategory[->, |*|] = SymmetricSemigroupalCategory.this
    }
}

object SymmetricSemigroupalCategory {
  trait Hoisted[G[_], ->[_, _], |*|[_, _]]
  extends SymmetricSemigroupalCategory[[a, b] =>> G[a -> b], |*|] {
    val applicative: Applicative[G]
    val base: SymmetricSemigroupalCategory[->, |*|]

    import applicative.{map2, pure}

    override def id[A]: G[A -> A] = pure(base.id)
    override def andThen[A, B, C](f: G[A -> B], g: G[B -> C]): G[A -> C] = map2(f, g)(base.andThen)
    override def par[A1, A2, B1, B2](f1: G[A1 -> B1], f2: G[A2 -> B2]): G[(A1 |*| A2) -> (B1 |*| B2)] = map2(f1, f2)(base.par)
    override def assocLR[A, B, C]: G[(A |*| B |*| C) -> (A |*| (B |*| C))] = pure(base.assocLR)
    override def assocRL[A, B, C]: G[(A |*| (B |*| C)) -> (A |*| B |*| C)] = pure(base.assocRL)
    override def swap[A, B]: G[(A |*| B) -> (B |*| A)] = pure(base.swap)
  }
}
