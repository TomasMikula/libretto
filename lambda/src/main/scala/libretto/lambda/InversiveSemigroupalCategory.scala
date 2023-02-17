package libretto.lambda

trait InversiveSemigroupalCategory[->[_, _], |*|[_, _], `-`[_]]
  extends ClosedSymmetricSemigroupalCategory[->, |*|, [x, y] =>> -[x] |*| y]
{
  def contrapositive[A, B](f: A -> B): -[B] -> -[A]

  /** Double inversion introduction. */
  def dii[A]: A -> -[-[A]]

  /** Double inversion elimination. */
  def die[A]: -[-[A]] -> A

  def portLR[A, B, C](f: (A |*| B) -> C): A -> (-[B] |*| C)

  def portRL[A, B, C](f: A -> (B |*| C)): (A |*| -[B]) -> C

  override def curry[A, B, C](f: (A |*| B) -> C): A -> (-[B] |*| C) =
    portLR(f)

  override def eval[A, B]: ((-[A] |*| B) |*| A) -> B =
    andThen(andThen(swap, snd(swap)), andThen(assocRL, portRL(id[A |*| B])))
}
