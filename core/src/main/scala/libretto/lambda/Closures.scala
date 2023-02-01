package libretto.lambda

import libretto.util.BiInjective

object Closures {
  def apply[-⚬[_, _], |*|[_, _], =⚬[_, _], V, E, LE](
    lambdas: Lambdas[-⚬, |*|, V, E, LE],
  )(using
    inj: BiInjective[|*|],
  ): Closures[-⚬, |*|, =⚬, V, E, LE, lambdas.type] =
    new Closures(lambdas)
}

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _], V, E, LE, LAMBDAS <: Lambdas[-⚬, |*|, V, E, LE]](
  val lambdas: LAMBDAS,
)(using
  inj: BiInjective[|*|],
) {
  import Lambdas.Abstracted
  import lambdas.{Abstracted, Expr}

  def app[A, B](
    f: Expr[A =⚬ B],
    a: Expr[A],
  )(
    auxVar: V,
    resultVar: V,
  )(using
    ctx: lambdas.Context,
    ev: ClosedSemigroupalCategory[-⚬, |*|, =⚬],
  ): Expr[B] =
    (f zip a)(auxVar).map(ev.eval[A, B])(resultVar)
}
