package libretto.impl

trait SymmetricMonoidalCategory[->[_, _], |*|[_, _], One]
  extends SymmetricSemigroupalCategory[->, |*|]
  with    MonoidalCategory[->, |*|, One]
