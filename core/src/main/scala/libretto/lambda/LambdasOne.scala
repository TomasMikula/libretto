package libretto.lambda

import libretto.util.BiInjective

class LambdasOne[-⚬[_, _], |*|[_, _], One, V](
  varSynthesizer: LambdasOne.VarSynthesizer[V, |*|],
)(using
  inj: BiInjective[|*|],
  smc: SymmetricMonoidalCategory[-⚬, |*|, One],
) extends Lambdas[-⚬, |*|, V, Lambdas.Error[V], Lambdas.Error.LinearityViolation[V]] {
  import varSynthesizer.newSyntheticVar

  type Error              = Lambdas.Error[V]
  val  Error              = Lambdas.Error
  type LinearityViolation = Lambdas.Error.LinearityViolation[V]
  val  LinearityViolation = Lambdas.Error.LinearityViolation

  val lambdas = LambdasImpl[-⚬, |*|, V, Error, LinearityViolation]

  override type AbstractFun[A, B] = lambdas.AbstractFun[A, B]
  override object AbstractFun extends AbstractFuns {
    export lambdas.AbstractFun.fold
  }

  override type Context = lambdas.Context
  override object Context extends Contexts {
    export lambdas.Context.{fresh, getDiscard, getSplit, nested, registerNonLinearOps}
  }

  type Var[A] = libretto.lambda.Var[V, A]

  sealed trait Expr[A] {
    def resultVar: Var[A] =
      this match
        case Expr.LambdasExpr(a) =>
          a.resultVar
        case Expr.OneExpr(v, t) =>
          t.terminalVarOpt match
            case Right(v) => v
            case Left(ev) => ev.substituteCo(v)
  }

  override object Expr extends Exprs {
    private[LambdasOne] case class LambdasExpr[A](value: lambdas.Expr[A]) extends Expr[A]
    private[LambdasOne] case class OneExpr[A](
      oneVar: Var[One],
      tail: OneTail[A],
    ) extends Expr[A]

    private[Expr] sealed trait OneTail[A] {
      import OneTail._

      def apply(expr: lambdas.Expr[One]): lambdas.Expr[A] =
        this match {
          case Id => expr
          case Map(init, f, v) => (init(expr) map f)(v)
          case Zip(t1, t2, v)  => (t1(expr) zip t2(expr))(v)
          case Prj1(t, v1, v2) => lambdas.Expr.unzip(t(expr))(v1, v2)._1
          case Prj2(t, v1, v2) => lambdas.Expr.unzip(t(expr))(v1, v2)._2
        }

      def apply(t: OneTail[One]): OneTail[A]

      def apply1(init: OneTail.OneTail1[One]): OneTail.OneTail1[A] =
        this match {
          case Id             => init
          case t: OneTail1[A] => t(init)
        }

      def terminalVarOpt: Either[One =:= A, Var[A]]
    }
    private[Expr] object OneTail {
      case object Id extends OneTail[One] {
        override def apply(t: OneTail[One]): OneTail[One] = t
        override def terminalVarOpt = Left(summon[One =:= One])
      }
      sealed trait OneTail1[A] extends OneTail[A] {
        override def apply(t: OneTail[One]): OneTail1[A] =
          this match {
            case Map(init, f, v) => Map(init(t), f, v)
            case Zip(t1, t2, v)  => Zip(t1(t), t2(t), v)
            case Prj1(xy, x, y)  => Prj1(xy(t), x, y)
            case Prj2(xy, x, y)  => Prj2(xy(t), x, y)
          }

        def terminalVar: Var[A] =
          this match {
            case Map(_, _, v)  => v
            case Zip(_, _, v)  => v
            case Prj1(_, v, _) => v
            case Prj2(_, _, v) => v
          }

        override def terminalVarOpt: Either[One =:= A, Var[A]] =
          Right(terminalVar)
      }
      case class Map[A, B](init: OneTail[A], f: A -⚬ B, resultVar: Var[B]) extends OneTail1[B]
      case class Zip[A1, A2](t1: OneTail1[A1], t2: OneTail1[A2], resultVar: Var[A1 |*| A2]) extends OneTail1[A1 |*| A2]
      case class Prj1[A, B](init: OneTail[A |*| B], resultVar: Var[A], residueVar: Var[B]) extends OneTail1[A]
      case class Prj2[A, B](init: OneTail[A |*| B], residueVar: Var[A], resultVar: Var[B]) extends OneTail1[B]

      def unzip[A, B](t: OneTail[A |*| B])(resultVar1: Var[A], resultVar2: Var[B]): (OneTail1[A], OneTail1[B]) =
        (Prj1(t, resultVar1, resultVar2), Prj2(t, resultVar1, resultVar2))
    }

    override def variable[A](v: Var[A]): Expr[A] =
      LambdasExpr(lambdas.Expr.variable(v))

    override def map[A, B](e: Expr[A], f: A -⚬ B, resultVar: Var[B]): Expr[B] =
      e match {
        case LambdasExpr(a) => LambdasExpr((a map f)(resultVar))
        case OneExpr(v, t)  => OneExpr(v, OneTail.Map(t, f, resultVar))
      }

    override def zip[A, B](a: Expr[A], b: Expr[B], resultVar: Var[A |*| B]): Expr[A |*| B] =
      (a, b) match {
        case (LambdasExpr(a), LambdasExpr(b)) =>
          LambdasExpr((a zip b)(resultVar))
        case (LambdasExpr(a), OneExpr(v, g)) =>
          val aOne: lambdas.Expr[A |*| One] =
            (a map smc.introSnd)(newSyntheticVar(Vars.single(a.resultVar) zip Vars.single(v)))
          val va = newSyntheticVar[A, A](hint = Vars.single(a.resultVar))
          val (a1, o1) = lambdas.Expr.unzip(aOne)(va, v)
          LambdasExpr(lambdas.Expr.zip(a1, g(o1), resultVar))
        case (OneExpr(v, f), LambdasExpr(b)) =>
          val oneB: lambdas.Expr[One |*| B] =
            (b map smc.introFst)(newSyntheticVar(Vars.single(v) zip Vars.single(b.resultVar)))
          val vb = newSyntheticVar[B, B](hint = Vars.single(b.resultVar))
          val (o1, b1) = lambdas.Expr.unzip(oneB)(v, vb)
          LambdasExpr(lambdas.Expr.zip(f(o1), b1, resultVar))
        case (a @ OneExpr(v, f), OneExpr(w, g)) =>
          val aOne: OneTail[A |*| One] =
            OneTail.Map(f, smc.introSnd, newSyntheticVar(Vars.single(a.resultVar) zip Vars.single(w)))
          val va = newSyntheticVar[A, A](hint = Vars.single(a.resultVar))
          val (a1, o1) = OneTail.unzip(aOne)(va, w)
          OneExpr(v, OneTail.Zip(a1, g.apply1(o1), resultVar))
      }

    override def unzip[B1, B2](e: Expr[B1 |*| B2])(resultVar1: Var[B1], resultVar2: Var[B2]): (Expr[B1], Expr[B2]) =
      e match {
        case LambdasExpr(e) =>
          val (b1, b2) = lambdas.Expr.unzip(e)(resultVar1, resultVar2)
          (LambdasExpr(b1), LambdasExpr(b2))
        case OneExpr(v, f) =>
          val (f1, f2) = OneTail.unzip(f)(resultVar1, resultVar2)
          (OneExpr(v, f1), OneExpr(v, f2))
      }

    override def resultVar[A](a: Expr[A]): Var[A] =
      a.resultVar

    def lift[A](expr: lambdas.Expr[A]): Expr[A] =
      LambdasExpr(expr)

    def one(v: Var[One]): Expr[One] =
      OneExpr(v, OneTail.Id)
  }

  override protected def eliminateVariable[A, B](boundVar: Var[A], expr: Expr[B])(using Context): Abstracted[A, B] =
    expr match {
      case Expr.LambdasExpr(b) =>
        lambdas.eliminateVariable(boundVar, b)
          .mapExpr[Expr]([X] => (x: lambdas.Expr[X]) => Expr.lift(x))
      case Expr.OneExpr(v, f) =>
        import Lambdas.Abstracted._
        val b = f(lambdas.Expr.variable(v))

        lambdas.eliminateVariable(boundVar, b) match {
          case Failure(e) =>
            Failure(e)
          case Closure(captured, f) =>
            captured.asBin match {
              case Bin.Leaf(x) =>
                lambdas.eliminateVariable(v, x) match
                  case Exact(g)      => Exact(lambdas.shuffled.lift(smc.introFst) > lambdas.shuffled.fst(g) > f)
                  case Closure(y, g) => throw AssertionError("Result of (f: OneExpr.Tail).apply(variable) can only capture that one variable, as OneExpr is not able to capture expressions.")
                  case Failure(e)    => Failure(e)
              case Bin.Branch(_, _) =>
                throw AssertionError("Result of (f: OneExpr.Tail).apply(variable) can only capture that one variable, as OneExpr is not able to capture expressions.")
            }
          case Exact(_) =>
            throw new AssertionError(s"Expected closure over variable $v")
        }
    }

  override def switch[<+>[_, _], A, B](
    cases: Sink[VFun, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    Context,
  ): AbsRes[A, B] =
    switchImpl(cases, sum, distribute)

  def compileConst[B](expr: Expr[B]): Either[Error, One -⚬ B] =
    expr match {
      case Expr.LambdasExpr(b) =>
        Left(Lambdas.Error.Undefined(b.initialVars))
      case Expr.OneExpr(v, f) =>
        import Lambdas.Abstracted.{Closure, Exact, Failure}
        val b = f(lambdas.Expr.variable(v))
        lambdas.eliminateVariable(v, b)(using Context.fresh()) match {
          case Exact(f) =>
            Right(f.fold)
          case Closure(captured, _) =>
            Left(Lambdas.Error.Undefined(
              captured.foldMap0(
                [x] => (ex: lambdas.Expr[x]) => ex.initialVars,
                _ merge _,
              )
            ))
          case Failure(e) =>
            Left(e)
        }
    }
}

object LambdasOne {
  trait VarSynthesizer[VarLabel, |*|[_, _]] {
    def newSyntheticVar[A, X](hint: Tupled[|*|, Var[VarLabel, *], X]): Var[VarLabel, A]
  }
}
