package libretto.lambda

trait MonoidalCategory[->[_, _], |*|[_, _], One]
  extends SemigroupalCategory[->, |*|]
{
  def introFst[A]: A -> (One |*| A)
  def introSnd[A]: A -> (A |*| One)

  def elimFst[A]: (One |*| A) -> A
  def elimSnd[A]: (A |*| One) -> A

  def introFst[A, X](f: One -> X): A -> (X |*| A) =
    introFst[A] > fst(f)

  def introSnd[A, X](f: One -> X): A -> (A |*| X) =
    introSnd[A] > snd(f)

  def elimFst[A, X](f: X -> One): (X |*| A) -> A =
    fst(f) > elimFst[A]

  def elimSnd[A, X](f: X -> One): (A |*| X) -> A =
    snd(f) > elimSnd[A]
}
