package libretto

trait InvertDSL extends ClosedDSL {
  type -[A]

  def backvert[A]: (A |*| -[A]) -⚬ One
  def forevert[A]: One -⚬ (-[A] |*| A)

  override type =⚬[A, B] = -[A] |*| B

  override def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B =
    andThen(swap, andThen(assocRL, elimFst(backvert)))

  override def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C) =
    andThen(introFst(forevert[B]), andThen(assocLR, par(id, andThen(swap, f))))
}
