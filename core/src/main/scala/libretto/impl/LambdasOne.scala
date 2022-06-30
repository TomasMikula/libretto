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
    export lambdas.VArr.{bimap, bimapZip, id, initialVars, map, par, terminalVars, unzip, zip}

    override def toExpr[A, B](f: VArr[A, B]): Expr[B] =
      Expr.LambdasExpr(lambdas.VArr.toExpr(f))
  }

  sealed trait Expr[A]

  override object Expr extends Exprs {
    private[LambdasOne] case class LambdasExpr[A](value: lambdas.Expr[A]) extends Expr[A]
    private[LambdasOne] case class OneExpr[A](value: lambdas.VArr[One, A]) extends Expr[A]

    override def variable[A](v: Var[A]): Expr[A] =
      LambdasExpr(lambdas.Expr.variable(v))

    override def map[A, B](e: Expr[A], f: A -⚬ B, resultVar: Var[B]): Expr[B] =
      e match {
        case LambdasExpr(a) => LambdasExpr((a map f)(resultVar))
        case OneExpr(g)     => OneExpr((g map f)(resultVar))
      }

    override def zip[A, B](a: Expr[A], b: Expr[B], resultVar: Var[A |*| B]): Expr[A |*| B] =
      (a, b) match {
        case (LambdasExpr(a), LambdasExpr(b)) =>
          LambdasExpr((a zip b)(resultVar))
        case (LambdasExpr(a), OneExpr(g)) =>
          val aOne: lambdas.Expr[A |*| One] =
            (a map smc.introSnd)(newSyntheticVar(a.terminalVars zip g.initialVars))
          val aId = lambdas.VArr.id[A](newSyntheticVar(hint = a.terminalVars))
          LambdasExpr(lambdas.Expr.bimapZip(aOne, aId, g, resultVar))
        case (OneExpr(f), LambdasExpr(b)) =>
          val oneB: lambdas.Expr[One |*| B] =
            (b map smc.introFst)(newSyntheticVar(f.initialVars zip b.terminalVars))
          val bId = lambdas.VArr.id[B](newSyntheticVar(hint = b.terminalVars))
          LambdasExpr(lambdas.Expr.bimapZip(oneB, f, bId, resultVar))
        case (OneExpr(f), OneExpr(g)) =>
          val aOne: lambdas.VArr[One, A |*| One] =
            (f map smc.introSnd)(newSyntheticVar(f.terminalVars zip g.initialVars))
          val aId = lambdas.VArr.id[A](newSyntheticVar(hint = f.terminalVars))
          OneExpr(lambdas.VArr.bimapZip(aOne, aId, g, resultVar))
      }

    override def par[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B] =
      (a, b) match {
        case (LambdasExpr(a), LambdasExpr(b)) =>
          LambdasExpr(a par b)
        case (LambdasExpr(a), OneExpr(g)) =>
          val aOne: lambdas.Expr[A |*| One] =
            (a map smc.introSnd)(newSyntheticVar(a.terminalVars zip g.initialVars))
          val aId = lambdas.VArr.id[A](newSyntheticVar(hint = a.terminalVars))
          LambdasExpr(lambdas.Expr.bimap(aOne, aId, g))
        case (OneExpr(f), LambdasExpr(b)) =>
          val oneB: lambdas.Expr[One |*| B] =
            (b map smc.introFst)(newSyntheticVar(f.initialVars zip b.terminalVars))
          val bId = lambdas.VArr.id[B](newSyntheticVar(hint = b.terminalVars))
          LambdasExpr(lambdas.Expr.bimap(oneB, f, bId))
        case (OneExpr(f), OneExpr(g)) =>
          val aOne: lambdas.VArr[One, A |*| One] =
            (f map smc.introSnd)(newSyntheticVar(f.terminalVars zip g.initialVars))
          val aId = lambdas.VArr.id[A](newSyntheticVar(hint = f.terminalVars))
          OneExpr(lambdas.VArr.bimap(aOne, aId, g))
      }

    override def bimap[A1, A2, B1, B2](a: Expr[A1 |*| A2], f1: VArr[A1, B1], f2: VArr[A2, B2]): Expr[B1 |*| B2] =
      a match {
        case LambdasExpr(a) => LambdasExpr(lambdas.Expr.bimap(a, f1, f2))
        case OneExpr(f)     => OneExpr(lambdas.VArr.bimap(f, f1, f2))
      }

    override def bimapZip[A1, A2, B1, B2](a: Expr[A1 |*| A2], f1: VArr[A1, B1], f2: VArr[A2, B2], resultVar: Var[B1 |*| B2]): Expr[B1 |*| B2] =
      a match {
        case LambdasExpr(a) => LambdasExpr(lambdas.Expr.bimapZip(a, f1, f2, resultVar))
        case OneExpr(f)     => OneExpr(lambdas.VArr.bimapZip(f, f1, f2, resultVar))
      }

    override def unzip[B1, B2](e: Expr[B1 |*| B2])(resultVar1: Var[B1], resultVar2: Var[B2]): (Expr[B1], Expr[B2]) =
      e match {
        case LambdasExpr(e) =>
          val (b1, b2) = lambdas.Expr.unzip(e)(resultVar1, resultVar2)
          (LambdasExpr(b1), LambdasExpr(b2))
        case OneExpr(f) =>
          val (b1, b2) = lambdas.VArr.unzip(f)(resultVar1, resultVar2)
          (OneExpr(b1), OneExpr(b2))
      }

    override def terminalVars[A](a: Expr[A]): Vars[A] =
      a match {
        case LambdasExpr(a) => a.terminalVars
        case OneExpr(a)     => a.terminalVars
      }

    def lift[A](expr: lambdas.Expr[A]): Expr[A] =
      LambdasExpr(expr)

    def one(v: Var[One]): Expr[One] =
      OneExpr(VArr.id(v))
  }

  override def abs[A, B](expr: Expr[B], boundVar: Var[A]): Abstracted[A, B] =
    expr match {
      case Expr.LambdasExpr(b) =>
        lambdas.abs(b, boundVar)
          .mapExpr[Expr]([X] => (x: lambdas.Expr[X]) => Expr.lift(x))
      case Expr.OneExpr(b) =>
        import Lambda.Abstracted._

        // boundVar will not be found,
        // because zipping with boundVar would produce LambdasExpr
        lambdas.abs(b.toExpr, boundVar) match {
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
      case Expr.OneExpr(b) =>
        // boundVar will not be found,
        // because zipping with boundVar would produce LambdasExpr
        lambdas.compile(lambdas.VArr.toExpr(b), boundVar) match {
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
