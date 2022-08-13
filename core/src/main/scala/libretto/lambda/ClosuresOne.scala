package libretto.lambda

import libretto.util.BiInjective

class ClosuresOne[-⚬[_, _], |*|[_, _], One, =⚬[_, _], Var[_], VarSet](using
  smc: SymmetricMonoidalCategory[-⚬, |*|, One],
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
) {
  val lambdas = new LambdasOne[-⚬, |*|, One, Var, VarSet](???)
}
