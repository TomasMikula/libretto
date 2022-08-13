package libretto.lambda

trait ClosedSymmetricSemigroupalCategory[->[_, _], |*|[_, _], -->[_, _]]
  extends ClosedSemigroupalCategory[->, |*|, -->]
  with    SymmetricSemigroupalCategory[->, |*|]
