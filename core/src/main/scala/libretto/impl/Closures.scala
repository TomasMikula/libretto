package libretto.impl

import libretto.BiInjective

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _], Var[_], VarSet](using
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
) {
  val lambdas = new Lambda[-⚬, |*|, Var, VarSet]
  import lambdas.{Abstracted, Expr, Var, shuffled}
  import shuffled.{Shuffled => ≈⚬}

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
  ): Either[ClosureError, Expr[A =⚬ B]] = {
    import ClosureError._

    lambdas.abs(f, boundVar) match {
      case Abstracted.Exact(_) =>
        Left(NoCapture("The closure does not capture any variables. Use an ordinary lambda instead"))
      case Abstracted.Closure(captured, f) =>
        Right((captured map ev.curry(f.fold))(resultVar))
      case Abstracted.Failure(e) =>
        Left(NonLinear(e))
    }
  }

  enum ClosureError {
    case NonLinear(e: lambdas.LinearityViolation)
    case NoCapture(msg: String)
  }
}
