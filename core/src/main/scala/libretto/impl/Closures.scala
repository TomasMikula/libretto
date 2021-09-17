package libretto.impl

import libretto.BiInjective

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _]](using
  inj: BiInjective[|*|],
) {
  val lambdas = new Lambda[-⚬, |*|]
  import lambdas.{Abstracted, Expr, Var, shuffled}
  import shuffled.{Shuffled => ≈⚬}

  def app[A, B](
    f: Expr[A =⚬ B],
    a: Expr[A],
  )(using
    ev: ClosedSemigroupalCategory[-⚬, |*|, =⚬],
  ): Expr[B] =
    (f zip a).map(ev.eval[A, B])

  def closure[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): Either[ClosureError, Expr[A =⚬ B]] = {
    import ClosureError._

    lambdas.abs(f) match {
      case Abstracted.Exact(_) =>
        Left(NoCapture("The closure does not capture any variables. Use an ordinary lambda instead"))
      case Abstracted.Closure(captured, f) =>
        val captured1 = captured.fold([x, y] => (ex: Expr[x], ey: Expr[y]) => ex zip ey)
        Right(captured1 map ev.curry(f.fold))
      case Abstracted.Failure(e) =>
        Left(NonLinear(e))
    }
  }

  enum ClosureError {
    case NonLinear(e: lambdas.LinearityViolation)
    case NoCapture(msg: String)
  }

  object ClosureError {
    def overused(v: Var[_]): ClosureError.NonLinear =
      NonLinear(lambdas.LinearityViolation.overused(v))

    def underused(v: Var[_]): ClosureError.NonLinear =
      NonLinear(lambdas.LinearityViolation.underused(v))

    def underused(vars: Set[Var[?]]): ClosureError.NonLinear =
      NonLinear(lambdas.LinearityViolation.Underused(vars))
  }
}
