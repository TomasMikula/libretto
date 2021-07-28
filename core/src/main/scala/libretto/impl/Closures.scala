package libretto.impl

import libretto.BiInjective

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _]](using
  inj: BiInjective[|*|],
) {
  val lambdas = new Lambda[-⚬, |*|]
  import lambdas.{AbsRes, Abstractable, ExprF, Vars, shuffled}
  import lambdas.Expr.Var

  sealed trait Closure[X, T] {
    def res: Var[T]
  }
  case class Closure0[X, A, B](f: (X |*| A) -⚬ B, captured: Vars[X], res: Var[A =⚬ B]) extends Closure[X, A =⚬ B]

  object Closure {
    implicit val abstractableClosure: Abstractable[Closure[?, *]] =
      new Abstractable[Closure[?, *]] {
        def abs[A, B](
          vars: Vars[A],
          expr: Closure[?, B],
          consumed: Set[Var[_]],
        ): AbsRes[A, B] =
          ??? // TODO
      }
  }

  type Expr[A] = lambdas.Expr[Closure[?, *], A]

  object Expr {
    def map[A, B](a: Expr[A], f: A -⚬ B): Expr[B] =
      a.map(f)

    def zip[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B] =
      lambdas.Expr.zip(a, b)

    def unzip[A, B](ab: Expr[A |*| B]): (Expr[A], Expr[B]) =
      lambdas.Expr.unzip(ab)([x] => (fx: Closure[?, x]) => fx.res)

    def app[A, B](
      f: Expr[A =⚬ B],
      a: Expr[A],
    )(using
      ev: ClosedSemigroupalCategory[-⚬, |*|, =⚬],
    ): Expr[B] =
      zip(f, a).map(ev.eval[A, B])
  }

  def abs[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: SymmetricSemigroupalCategory[-⚬, |*|],
  ): Either[lambdas.Error, A -⚬ B] =
    lambdas.abs(f)

  def closure[A, B, =⚬[_, _]](
    f: Expr[A] => Expr[B],
  )(using
    ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): Either[ClosureError, Expr[A =⚬ B]] = {
    val a = new Var[A]()
    val b = f(a)
    lambdas.abs(
      Vars.Single(a),
      b,
      consumed = Set.empty,
    ) match {
      case AbsRes.Exact(_, _) => Left(ClosureError.NoCapture("The closure does not capture any variables. Use an ordinary lambda instead"))
      // TODO
    }
  }

  enum ClosureError {
    case NonLinear(e: lambdas.LinearityViolation)
    case NoCapture(msg: String)
  }
}
