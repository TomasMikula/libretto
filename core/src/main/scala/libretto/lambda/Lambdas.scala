package libretto.lambda

import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.util.BiInjective
import scala.annotation.targetName

trait Lambdas[-⚬[_, _], |*|[_, _], Var[_], VarSet, E, LE] {
  final type Tupled[F[_], A] = libretto.lambda.Tupled[|*|, F, A]

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

  def abs[A, B](
    f: Expr[A] => Expr[B],
    bindVar: Var[A],
  ): Abstracted[A, B] =
    abs(f(Expr.variable(bindVar)), bindVar)
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

    def overusedVar[Var[_], VarSet, A](v: Var[A])(using
      ev: Variable[Var, VarSet],
    ): LinearityViolation[VarSet] =
      LinearityViolation.Overused(ev.singleton(v))

    def underusedVar[Var[_], VarSet, A](v: Var[A])(using
      ev: Variable[Var, VarSet],
    ): LinearityViolation[VarSet] =
      LinearityViolation.Underused(ev.singleton(v))

    def undefinedVar[Var[_], VarSet, A](v: Var[A])(using
      ev: Variable[Var, VarSet],
    ): Error[VarSet] =
      Undefined(ev.singleton(v))
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
        case Exact(u, f)             => Exact(u, f)
        case Closure(captured, u, f) => Closure(g(captured), u, f)
        case NotFound(b)             => NotFound(g(b))
        case Failure(e)              => Failure(e)
      }
  }

  object Abstracted {
    case class Exact[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, A1, B](
      m: Multiplier[|*|, A, A1],
      f: AbsFun[A1, B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class Closure[Exp[_], |*|[_, _], AbsFun[_, _], LE, X, A, A1, B](
      captured: Exp[X],
      m: Multiplier[|*|, A, A1],
      f: AbsFun[X |*| A1, B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class NotFound[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B](
      b: Exp[B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class Failure[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B](
      e: LE,
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]
  }
}
