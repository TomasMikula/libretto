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
    resultVar: Var[B],
  )(using
    ev: ClosedSemigroupalCategory[-⚬, |*|, =⚬],
  ): Expr[B] =
    (f par a).map(ev.eval[A, B])(resultVar)

  def closure[A, B](
    f: Expr[A] => Expr[B],
    boundVar: Var[A],
  )(using
    ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): ClosureRes[A, B] = {
    import ClosureRes._

    lambdas.abs(f(Expr.variable(boundVar)), boundVar) match {
      case Abstracted.Exact(m, f) =>
        NonCapturing(m, f.fold)
      case Abstracted.Closure(captured, m, f) =>
        Capturing(captured, m, f.fold)
      case Abstracted.NotFound(b) =>
        NotFound(b)
      case Abstracted.Failure(e) =>
        NonLinear(e)
    }
  }

  /**
   * @tparam LE type that represents linearity violation
   */
  sealed trait ClosureRes[A, B]
  object ClosureRes {
    case class Capturing[X, A, A1, B](
      captured: Expr[X],
      m: Multiplier[|*|, A, A1],
      f: (X |*| A1) -⚬ B,
    ) extends ClosureRes[A, B]

    case class NonCapturing[A, A1, B](
      m: Multiplier[|*|, A, A1],
      f: A1 -⚬ B,
    ) extends ClosureRes[A, B]

    case class NotFound[A, B](b: Expr[B]) extends ClosureRes[A, B]
    case class NonLinear[A, B](e: LE) extends ClosureRes[A, B]
  }
}
