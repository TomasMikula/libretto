package libretto.impl

import libretto.impl.Lambdas.Error.LinearityViolation
import libretto.util.BiInjective
import scala.annotation.targetName

trait Lambdas[-⚬[_, _], |*|[_, _], Var[_], VarSet, E, LE] {
  final type Tupled[F[_], A] = libretto.impl.Tupled[|*|, F, A]

  final type Vars[A] = Tupled[Var, A]

  object Vars {
    def single[A](a: Var[A]): Vars[A] =
      Tupled.Single(a)

    def bi[A, B](a: Var[A], b: Var[B]): Vars[A |*| B] =
      zip(single(a), single(b))

    def zip[A, B](a: Vars[A], b: Vars[B]): Vars[A |*| B] =
      Tupled.Zip(a, b)

    def unzip[A, B](ab: Vars[A |*| B]): Option[(Vars[A], Vars[B])] =
      Tupled.unzip(ab)

    def sameVars[A](a: Vars[A], b: Vars[A]): Boolean =
      (a isEqualTo b)([X] => (x: Var[X], y: Var[X]) => x == y)

    def toSet[A](vars: Vars[A])(using variables: Variable[Var, VarSet]): VarSet =
      vars.mapReduce0(
        map    = [x] => (v: Var[x]) => variables.singleton(v),
        reduce = variables.union(_, _),
      )
  }

  extension [A](vars: Vars[A]) {
    def toSet(using variables: Variable[Var, VarSet]): VarSet =
      Vars.toSet(vars)
  }

  type VArr[A, B]
  val VArr: VArrs

  trait VArrs {
    def id[A](a: Var[A]): VArr[A, A]
    def map[A, B, C](f: VArr[A, B], g: B -⚬ C, resultVar: Var[C]): VArr[A, C]
    def zip[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2], resultVar: Var[B1 |*| B2]): VArr[A1 |*| A2, B1 |*| B2]
    def par[A1, A2, B1, B2](f1: VArr[A1, B1], f2: VArr[A2, B2]): VArr[A1 |*| A2, B1 |*| B2]
    def unzip[A, B1, B2](f: VArr[A, B1 |*| B2])(resultVar1: Var[B1], resultVar2: Var[B2]): (VArr[A, B1], VArr[A, B2])
    def initialVars[A, B](f: VArr[A, B]): Vars[A]
    def terminalVars[A, B](f: VArr[A, B]): Vars[B]
    def toExpr[A, B](f: VArr[A, B]): Expr[B]
  }

  extension [A, B](f: VArr[A, B]) {
    @targetName("varrMap")
    def map[C](g: B -⚬ C)(resultVar: Var[C]): VArr[A, C] =
      VArr.map(f, g, resultVar)

    @targetName("varrZip")
    def zip[A2, B2](g: VArr[A2, B2])(resultVar: Var[B |*| B2]): VArr[A |*| A2, B |*| B2] =
      VArr.zip(f, g, resultVar)

    @targetName("varrInitialVars")
    def initialVars: Vars[A] =
      VArr.initialVars(f)

    @targetName("varrTerminalVars")
    def terminalVars: Vars[B] =
      VArr.terminalVars(f)

    @targetName("varrToExpr")
    def toExpr: Expr[B] =
      VArr.toExpr(f)
  }

  type Expr[A]
  val Expr: Exprs

  trait Exprs {
    def variable[A](a: Var[A]): Expr[A]
    def map[A, B](e: Expr[A], f: A -⚬ B, resultVar: Var[B]): Expr[B]
    def zip[A, B](a: Expr[A], b: Expr[B], resultVar: Var[A |*| B]): Expr[A |*| B]
    def par[A, B](a: Expr[A], b: Expr[B]): Expr[A |*| B]
    def unzip[A, B](ab: Expr[A |*| B])(resultVar1: Var[A], resultVar2: Var[B]): (Expr[A], Expr[B])
    def terminalVars[A](a: Expr[A]): Vars[A]
  }

  extension [A](a: Expr[A]) {
    @targetName("exprMap")
    def map[B](f: A -⚬ B)(resultVar: Var[B]): Expr[B] =
      Expr.map(a, f, resultVar)

    @targetName("exprZip")
    def zip[B](b: Expr[B])(resultVar: Var[A |*| B]): Expr[A |*| B] =
      Expr.zip(a, b, resultVar)

    @targetName("exprPar")
    def par[B](b: Expr[B]): Expr[A |*| B] =
      Expr.par(a, b)

    @targetName("exprTerminalVars")
    def terminalVars: Vars[A] =
      Expr.terminalVars(a)
  }

  type AbstractFun[A, B]
  val AbstractFun: AbstractFuns

  trait AbstractFuns {
    def fold[A, B](f: AbstractFun[A, B]): A -⚬ B
  }

  extension [A, B](f: AbstractFun[A, B]) {
    def fold: A -⚬ B =
      AbstractFun.fold(f)
  }

  type Abstracted[A, B] = Lambdas.Abstracted[Expr, |*|, AbstractFun, LE, A, B]

  def abs[A, B](
    expr: Expr[B],
    boundVar: Var[A],
  ): Abstracted[A, B]

  def compile[A, B](
    expr: Expr[B],
    boundVar: Var[A],
  ): Either[E, A -⚬ B]

  def compile[A, B](
    f: Expr[A] => Expr[B],
    boundVar: Var[A],
  ): Either[E, A -⚬ B] =
    compile(f(Expr.variable(boundVar)), boundVar)
}

object Lambdas {
  def apply[-⚬[_, _], |*|[_, _], Var[_], VarSet, E, LE](using
  ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
    variables: Variable[Var, VarSet],
    errors: ErrorFactory[E, LE, VarSet],
  ): Lambdas[-⚬, |*|, Var, VarSet, E, LE] =
    new LambdasImpl[-⚬, |*|, Var, VarSet, E, LE]

  sealed trait Error[VarSet]
  object Error {
    case class Undefined[VarSet](vars: VarSet) extends Error[VarSet]

    sealed trait LinearityViolation[VarSet] extends Error[VarSet]

    object LinearityViolation {
      case class Overused[VarSet](vars: VarSet) extends LinearityViolation[VarSet]

      case class Underused[VarSet](vars: VarSet) extends LinearityViolation[VarSet]
    }
  }

  trait ErrorFactory[E, LE, VarSet] {
    def underusedVars(vs: VarSet): LE
    def overusedVars(vs: VarSet): LE

    def undefinedVars(vs: VarSet): E

    def fromLinearityViolation(e: LE): E
  }

  object ErrorFactory {
    given canonicalInstance[VarSet]: ErrorFactory[Error[VarSet], LinearityViolation[VarSet], VarSet] with {
      override def overusedVars(vs: VarSet): LinearityViolation[VarSet] = LinearityViolation.Overused(vs)
      override def underusedVars(vs: VarSet): LinearityViolation[VarSet] = LinearityViolation.Underused(vs)
      override def undefinedVars(vs: VarSet): Error[VarSet] = Error.Undefined(vs)
      override def fromLinearityViolation(e: LinearityViolation[VarSet]): Error[VarSet] = e
    }
  }

  sealed trait Abstracted[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B] {
    import Abstracted._

    def mapExpr[Exp2[_]](g: [X] => Exp[X] => Exp2[X]): Abstracted[Exp2, |*|, AbsFun, LE, A, B] =
      this match {
        case Exact(f)             => Exact(f)
        case Closure(captured, f) => Closure(g(captured), f)
        case Failure(e)           => Failure(e)
      }
  }

  object Abstracted {
    case class Exact[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B](
      f: AbsFun[A, B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class Closure[Exp[_], |*|[_, _], AbsFun[_, _], LE, X, A, B](
      captured: Exp[X],
      f: AbsFun[X |*| A, B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class Failure[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B](
      e: LE,
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]
  }
}
