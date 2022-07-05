package libretto.impl

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
    resultVar: Var[A =⚬ B],
  )(using
    ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): Either[ClosureError[LE], Expr[A =⚬ B]] = {
    import ClosureError._

    lambdas.abs(f(Expr.variable(boundVar)), boundVar) match {
      case Abstracted.Exact(_) =>
        Left(NoCapture("The closure does not capture any variables. Use an ordinary lambda instead"))
      case Abstracted.Closure(captured, f) =>
        Right((captured map ev.curry(f.fold))(resultVar))
      case Abstracted.Failure(e) =>
        Left(NonLinear(e))
    }
  }

  /**
   * @tparam LE type that represents linearity violation
   */
  enum ClosureError[LE] {
    case NonLinear(e: LE)
    case NoCapture(msg: String)
  }
}
