package libretto.impl

trait MonoidalCategory[->[_, _], |*|[_, _], One]
  extends SemigroupalCategory[->, |*|]
{
  def introFst[A]: A -> (One |*| A)
  def introSnd[A]: A -> (A |*| One)

  def elimFst[A]: (One |*| A) -> A
  def elimSnd[A]: (A |*| One) -> A
}
