package libretto.lambda

trait ClosedSymmetricMonoidalCategory[-⚬[_, _], |*|[_, _], One, =⚬[_, _]]
  extends ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬]
  with    SymmetricMonoidalCategory[-⚬, |*|, One]
