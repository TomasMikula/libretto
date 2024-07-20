package libretto.cats

trait Affine[->[_, _], One, A] {
  def discard: A -> One
}

object Affine {
  def from[->[_, _], One, A](f: A -> One): Affine[->, One, A] =
    new Affine[->, One, A] {
      override def discard: A -> One =
        f
    }
}
