package libretto.impl

import libretto.BiInjective

class LambdasOne[-⚬[_, _], |*|[_, _], One, Var[_], VarSet](
  varSynthesizer: LambdasOne.VarSynthesizer[Var, |*|],
)(using
  inj: BiInjective[|*|],
  variables: Variable[Var, VarSet],
  smc: SymmetricMonoidalCategory[-⚬, |*|, One],
) extends Lambda[-⚬, |*|, Var, VarSet, Lambda.Error[VarSet], Lambda.Error.LinearityViolation[VarSet]] {
  import varSynthesizer.newSyntheticVar

  type Error              = Lambda.Error[VarSet]
  val  Error              = Lambda.Error
  type LinearityViolation = Lambda.Error.LinearityViolation[VarSet]
  val  LinearityViolation = Lambda.Error.LinearityViolation

  val lambdas = Lambda[-⚬, |*|, Var, VarSet, Error, LinearityViolation]

  override type AbstractFun[A, B] = lambdas.AbstractFun[A, B]
  override object AbstractFun extends AbstractFuns {
    export lambdas.AbstractFun.fold
  }

  override type VArr[A, B] = lambdas.VArr[A, B]

  override object VArr extends VArrs {
    export lambdas.VArr.{id, initialVars, map, par, terminalVars, unzip, zip}

    override def toExpr[A, B](f: VArr[A, B]): Expr[B] =
      Expr.LambdasExpr(lambdas.VArr.toExpr(f))
  }

  sealed trait Expr[A]

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
          case Par(t1, t2)     => t1(expr) par t2(expr)
          case Prj1(t, v1, v2) => lambdas.Expr.unzip(t(expr))(v1, v2)._1
          case Prj2(t, v1, v2) => lambdas.Expr.unzip(t(expr))(v1, v2)._2
        }

      def apply(t: OneTail[One]): OneTail[A]

      def apply1(init: OneTail.OneTail1[One]): OneTail.OneTail1[A] =
        this match {
          case Id             => init
          case t: OneTail1[A] => t(init)
        }

      def terminalVarsOpt: Option[Vars[A]]
    }
    private[Expr] object OneTail {
      case object Id extends OneTail[One] {
        override def apply(t: OneTail[One]): OneTail[One] = t
        override def terminalVarsOpt = None
      }
      sealed trait OneTail1[A] extends OneTail[A] {
        override def apply(t: OneTail[One]): OneTail1[A] =
          this match {
            case Map(init, f, v) => Map(init(t), f, v)
            case Zip(t1, t2, v)  => Zip(t1(t), t2(t), v)
            case Par(t1, t2)     => Par(t1(t), t2(t))
            case Prj1(xy, x, y)  => Prj1(xy(t), x, y)
            case Prj2(xy, x, y)  => Prj2(xy(t), x, y)
          }

        def terminalVars: Vars[A] =
          this match {
            case Map(_, _, v)  => Vars.single(v)
            case Zip(_, _, v)  => Vars.single(v)
            case Par(t1, t2)   => t1.terminalVars zip t2.terminalVars
            case Prj1(_, v, _) => Vars.single(v)
            case Prj2(_, _, v) => Vars.single(v)
          }

        override def terminalVarsOpt: Option[Vars[A]] =
          Some(terminalVars)
      }
      case class Map[A, B](init: OneTail[A], f: A -⚬ B, resultVar: Var[B]) extends OneTail1[B]
      case class Zip[A1, A2](t1: OneTail1[A1], t2: OneTail1[A2], resultVar: Var[A1 |*| A2]) extends OneTail1[A1 |*| A2]
      case class Par[A1, A2](t1: OneTail1[A1], t2: OneTail1[A2]) extends OneTail1[A1 |*| A2]
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
            (a map smc.introSnd)(newSyntheticVar(a.terminalVars zip Vars.single(v)))
          val va = newSyntheticVar[A](hint = a.terminalVars)
          val (a1, o1) = lambdas.Expr.unzip(aOne)(va, v)
          LambdasExpr(lambdas.Expr.zip(a1, g(o1), resultVar))
        case (OneExpr(v, f), LambdasExpr(b)) =>
          val oneB: lambdas.Expr[One |*| B] =
            (b map smc.introFst)(newSyntheticVar(Vars.single(v) zip b.terminalVars))
          val vb = newSyntheticVar[B](hint = b.terminalVars)
          val (o1, b1) = lambdas.Expr.unzip(oneB)(v, vb)
          LambdasExpr(lambdas.Expr.zip(f(o1), b1, resultVar))
        case (a @ OneExpr(v, f), OneExpr(w, g)) =>
          val aOne: OneTail[A |*| One] =
            OneTail.Map(f, smc.introSnd, newSyntheticVar(a.terminalVars zip Vars.single(w)))
          val va = newSyntheticVar[A](hint = a.terminalVars)
          val (a1, o1) = OneTail.unzip(aOne)(va, w)
          OneExpr(v, OneTail.Zip(a1, g.apply1(o1), resultVar))
      }

    override def par[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B] =
      (a, b) match {
        case (LambdasExpr(a), LambdasExpr(b)) =>
          LambdasExpr(a par b)
        case (LambdasExpr(a), OneExpr(v, g)) =>
          val aOne: lambdas.Expr[A |*| One] =
            (a map smc.introSnd)(newSyntheticVar(a.terminalVars zip Vars.single(v)))
          val va = newSyntheticVar[A](hint = a.terminalVars)
          val (a1, o1) = lambdas.Expr.unzip(aOne)(va, v)
          LambdasExpr(lambdas.Expr.par(a1, g(o1)))
        case (OneExpr(v, f), LambdasExpr(b)) =>
          val oneB: lambdas.Expr[One |*| B] =
            (b map smc.introFst)(newSyntheticVar(Vars.single(v) zip b.terminalVars))
          val vb = newSyntheticVar[B](hint = b.terminalVars)
          val (o1, b1) = lambdas.Expr.unzip(oneB)(v, vb)
          LambdasExpr(lambdas.Expr.par(f(o1), b1))
        case (a @ OneExpr(v, f), OneExpr(w, g)) =>
          val aOne: OneTail[A |*| One] =
            OneTail.Map(f, smc.introSnd, newSyntheticVar(a.terminalVars zip Vars.single(w)))
          val va = newSyntheticVar[A](hint = a.terminalVars)
          val (a1, o1) = OneTail.unzip(aOne)(va, w)
          OneExpr(v, OneTail.Par(a1, g.apply1(o1)))
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

    override def terminalVars[A](a: Expr[A]): Vars[A] =
      a match {
        case LambdasExpr(a) => a.terminalVars
        case OneExpr(v, f)  => a.terminalVars
      }

    def lift[A](expr: lambdas.Expr[A]): Expr[A] =
      LambdasExpr(expr)

    def one(v: Var[One]): Expr[One] =
      OneExpr(v, OneTail.Id)
  }

  override def abs[A, B](expr: Expr[B], boundVar: Var[A]): Abstracted[A, B] =
    expr match {
      case Expr.LambdasExpr(b) =>
        lambdas.abs(b, boundVar)
          .mapExpr[Expr]([X] => (x: lambdas.Expr[X]) => Expr.lift(x))
      case Expr.OneExpr(v, f) =>
        import Lambda.Abstracted._
        val b = f(lambdas.Expr.variable(v))

        // boundVar will not be found,
        // because zipping with boundVar would produce LambdasExpr
        lambdas.abs(b, boundVar) match {
          case Failure(e) =>
            Failure(e)
          case Exact(_) | Closure(_, _) =>
            throw new AssertionError(s"Did not expect to find variable $boundVar in $b, because $b is a constant expression")
        }
    }

  override def compile[A, B](
    expr: Expr[B],
    boundVar: Var[A],
  ): Either[Error, A -⚬ B] =
    expr match {
      case Expr.LambdasExpr(b) =>
        lambdas.compile(b, boundVar)
      case Expr.OneExpr(v, f) =>
        val b = f(lambdas.Expr.variable(v))

        // boundVar will not be found,
        // because zipping with boundVar would produce LambdasExpr
        lambdas.compile(b, boundVar) match {
          case Left(e) =>
            Left(e)
          case Right(f) =>
            throw new AssertionError(s"Did not expect to find variable $boundVar in $b, because $b is a constant expression")
        }
    }
}

object LambdasOne {
  trait VarSynthesizer[Var[_], |*|[_, _]] {
    def newSyntheticVar[A](hint: Tupled[|*|, Var, ?]): Var[A]
  }
}
