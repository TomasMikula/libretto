package libretto.lambda

import libretto.util.BiInjective

object Closures {
  def apply[-⚬[_, _], |*|[_, _], =⚬[_, _], Var[_], VarSet, E, LE](
    lambdas: Lambdas[-⚬, |*|, Var, VarSet, E, LE],
  )(using
    inj: BiInjective[|*|],
    variables: Variable[Var, VarSet],
  ): Closures[-⚬, |*|, =⚬, Var, VarSet, E, LE, lambdas.type] =
    new Closures(lambdas)
}

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _], Var[_], VarSet, E, LE, LAMBDAS <: Lambdas[-⚬, |*|, Var, VarSet, E, LE]](
  val lambdas: LAMBDAS,
)(using
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
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

  def closure[A, B](
    boundVar: Var[A],
    f: lambdas.Context ?=> Expr[A] => Expr[B],
  )(using
    ctx: lambdas.Context,
    ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): ClosureRes[A, B] = {
    import ClosureRes._

    lambdas.absNested(boundVar, f) match {
      case Abstracted.Exact(f) =>
        NonCapturing(f.fold)
      case Abstracted.Closure(captured, f) =>
        Capturing(captured, f.fold)
      case Abstracted.Failure(e) =>
        NonLinear(e)
    }
  }

  /**
   * @tparam LE type that represents linearity violation
   */
  sealed trait ClosureRes[A, B]
  object ClosureRes {
    case class Capturing[X, A, B](
      captured: Tupled[|*|, Expr, X],
      f: (X |*| A) -⚬ B,
    ) extends ClosureRes[A, B]

    case class NonCapturing[A, B](
      f: A -⚬ B,
    ) extends ClosureRes[A, B]

    case class NonLinear[A, B](e: LE) extends ClosureRes[A, B]
  }
}
