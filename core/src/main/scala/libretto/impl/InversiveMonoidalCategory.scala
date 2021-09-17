package libretto.impl

trait InversiveMonoidalCategory[->[_, _], |*|[_, _], One, `-`[_]]
  extends InversiveSemigroupalCategory[->, |*|, -]
  with    SymmetricMonoidalCategory[->, |*|, One]
{
  def backvert[A]: (A |*| -[A]) -> One
  def forevert[A]: One -> (-[A] |*| A)

  override def contrapositive[A, B](f: A -> B): -[B] -> -[A] =
    introFst[-[B]] > fst(forevert[A] > snd(f)) > assocLR > snd(backvert[B]) > elimSnd

  override def dii[A]: A -> -[-[A]] =
    introSnd[A] > snd(forevert[-[A]] > swap) > assocRL > fst(backvert[A]) > elimFst

  override def die[A]: -[-[A]] -> A =
    introFst[-[-[A]]] > fst(forevert[A] > swap) > assocLR > snd(backvert[-[A]]) > elimSnd

  override def portLR[A, B, C](f: (A |*| B) -> C): A -> (-[B] |*| C) =
    introFst[A] > fst(forevert[B]) > assocLR > snd(swap > f)

  override def portRL[A, B, C](f: A -> (B |*| C)): (A |*| -[B]) -> C =
    fst(f > swap) > assocLR > snd(backvert[B]) > elimSnd
}
