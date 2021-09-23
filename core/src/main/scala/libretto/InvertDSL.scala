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

  override def out[A, B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
    snd(f)

  def contrapositive[A, B](f: A -⚬ B): -[B] -⚬ -[A] =
    andThen(introFst(andThen(forevert[A], snd(f))), andThen(assocLR, elimSnd(backvert[B])))

  /** Double-inversion elimination. */
  def die[A]: -[-[A]] -⚬ A =
    andThen(introSnd(forevert[A]), andThen(assocRL, elimFst(andThen(swap, backvert[-[A]]))))

  /** Double-inversion introduction. */
  def dii[A]: A -⚬ -[-[A]] =
    andThen(introFst(forevert[-[A]]), andThen(assocLR, elimSnd(andThen(swap, backvert[A]))))
}
