package libretto.lambda

import libretto.util.BiInjective

object Closures {
  def apply[-⚬[_, _], |*|[_, _], =⚬[_, _], Var[_], VarSet, E, LE](
    lambdas: Lambdas[-⚬, |*|, Var, VarSet, E, LE],
  )(using
    inj: BiInjective[|*|],
    variables: Variables[Var, VarSet],
  ): Closures[-⚬, |*|, =⚬, Var, VarSet, E, LE, lambdas.type] =
    new Closures(lambdas)
}

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _], Var[_], VarSet, E, LE, LAMBDAS <: Lambdas[-⚬, |*|, Var, VarSet, E, LE]](
  val lambdas: LAMBDAS,
)(using
  inj: BiInjective[|*|],
  variables: Variables[Var, VarSet],
) {
  import Lambdas.Abstracted
  import lambdas.{Abstracted, Expr, Var}

  def app[A, B](
    f: Expr[A =⚬ B],
    a: Expr[A],
  )(
    auxVar: Var[(A =⚬ B) |*| A],
    resultVar: Var[B],
  )(using
    ev: ClosedSemigroupalCategory[-⚬, |*|, =⚬],
  ): Expr[B] =
    (f zip a)(auxVar).map(ev.eval[A, B])(resultVar)
}
