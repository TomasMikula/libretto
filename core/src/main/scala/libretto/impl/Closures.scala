package libretto.impl

import libretto.BiInjective

class Closures[-⚬[_, _], |*|[_, _], =⚬[_, _]](using
  inj: BiInjective[|*|],
) {
  val lambdas = new Lambda[-⚬, |*|]
  import lambdas.{AbsRes, Abstractable, ExprF, Vars, shuffled}
  import lambdas.Expr.Var
  import shuffled.{Shuffled => ≈⚬}

  sealed trait Closure[X, T] {
    def res: Var[T]

    def abs[Z](
      vars: Vars[Z],
      consumed: Set[Var[_]],
    )(using
      ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
    ): AbsRes[Z, T]
  }

  case class Closure0[X, A, B](f: (X |*| A) ≈⚬ B, captured: Vars[X], res: Var[A =⚬ B]) extends Closure[X, A =⚬ B] {
    override def abs[Z](
      vars: Vars[Z],
      consumed: Set[Var[_]],
    )(using
      ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
    ): AbsRes[Z, A =⚬ B] = {
      import Vars.Cmp._

      (vars compare captured) match {
        case Disjoint() => AbsRes.Failure.underused(vars.toSet)
        case Iso(s)     => AbsRes.Exact(shuffled.lift(ev.andThen(s.fold, ev.curry(f.fold))), consumed ++ vars.toSet)
        case other      => ??? // TODO
      }
    }
  }

  object Closure {
    implicit def abstractableClosure(using
      ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
    ): Abstractable[Closure[?, *]] =
      new Abstractable[Closure[?, *]] {
        def abs[A, B](
          vars: Vars[A],
          expr: Closure[?, B],
          consumed: Set[Var[_]],
        ): AbsRes[A, B] =
          expr.abs(vars, consumed)
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

    def closure[X, A, B](f: (X |*| A) ≈⚬ B, captured: Vars[X]): Expr[A =⚬ B] =
      lambdas.Expr.Ext(Closure0(f, captured, new Var[A =⚬ B]))
  }

  def abs[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): Either[lambdas.Error, A -⚬ B] =
    lambdas.abs(f)

  def closure[A, B](
    f: Expr[A] => Expr[B],
  )(using
    ev: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬],
  ): Either[ClosureError, Expr[A =⚬ B]] = {
    import ClosureError._

    val a = new Var[A]()
    val b = f(a)
    lambdas.abs(
      Vars.single(a),
      b,
      consumed = Set.empty,
    ) match {
      case AbsRes.Exact(_, _) =>
        Left(NoCapture("The closure does not capture any variables. Use an ordinary lambda instead"))
      case AbsRes.Partial(_, _, _) =>
        Left(NoCapture("The closure does not capture any variables. Use an ordinary lambda instead"))
      case AbsRes.Closure(f, captured, _) =>
        Right(Expr.closure(f, captured))
      case AbsRes.PartialClosure(_, _, _, _) =>
        println(s"$a is underused")
        Left(underused(a))
      case AbsRes.Failure(e) =>
        println(s"Failure: $e")
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
  }
}
