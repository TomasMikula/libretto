package libretto.lambda

import libretto.util.BiInjective

object Closures {
  def apply[-⚬[_, _], |*|[_, _], =⚬[_, _], VarLabel, E, LE](
    lambdas: Lambdas[-⚬, |*|, VarLabel, E, LE],
  )(using
    inj: BiInjective[|*|],
  ): Closures[-⚬, |*|, =⚬, VarLabel, E, LE, lambdas.type] =
    new Closures(lambdas)
}

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _], VarLabel, E, LE, LAMBDAS <: Lambdas[-⚬, |*|, VarLabel, E, LE]](
  val lambdas: LAMBDAS,
)(using
  inj: BiInjective[|*|],
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
