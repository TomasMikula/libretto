package libretto.lambda

import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.util.{BiInjective, Semigroup}
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
    def unzip[A, B](ab: Expr[A |*| B])(resultVar1: Var[A], resultVar2: Var[B]): (Expr[A], Expr[B])

    def resultVar[A](a: Expr[A]): Var[A]
  }

  extension [A](a: Expr[A]) {
    @targetName("exprMap")
    def map[B](f: A -⚬ B)(resultVar: Var[B]): Expr[B] =
      Expr.map(a, f, resultVar)

    @targetName("exprZip")
    def zip[B](b: Expr[B])(resultVar: Var[A |*| B]): Expr[A |*| B] =
      Expr.zip(a, b, resultVar)

    @targetName("exprResultVar")
    def resultVar: Var[A] =
      Expr.resultVar(a)
  }

  type Context
  val Context: Contexts

  trait Contexts {
    def fresh(): Context

    def registerNonLinearOps[A](v: Var[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(using
      Context
    ): Unit

    def getSplit[A](v: Var[A])(using Context): Option[A -⚬ (A |*| A)]

    def getDiscard[A](v: Var[A])(using Context): Option[[B] => Unit => (A |*| B) -⚬ B]
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

  protected def eliminateVariable[A, B](
    boundVar: Var[A],
    expr: Expr[B],
  )(using Context): Abstracted[A, B]

  def abs[A, B](
    bindVar: Var[A],
    f: Context ?=> Expr[A] => Expr[B],
  ): Abstracted[A, B] = {
    given Context = Context.fresh()
    eliminateVariable(bindVar, f(Expr.variable(bindVar)))
  }

  type VFun[A, B] = (Var[A], Expr[A] => Expr[B])

  def switch[<+>[_, _], A, B](
    scrutinee: Expr[A],
    patterns: Sink[VFun, <+>, A, B],
    // distribute: [x, y, z] => (x |*| (y <+> z)) -⚬ ((x |*| y) <+> (x |*| z))
  ): Expr[B]
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

    sealed trait LinearityViolation[VarSet] extends Error[VarSet] {
      import LinearityViolation._

      def combine(that: LinearityViolation[VarSet])(using ev: Semigroup[VarSet]): LinearityViolation[VarSet] =
        (this, that) match {
          case (Overused(s),     Overused(t)    ) => Overused(ev.combine(s, t))
          case (Overused(s),     Underused(t)   ) => OverUnder(s, t)
          case (Overused(s),     OverUnder(t, u)) => OverUnder(ev.combine(s, t), u)
          case (Underused(s),    Overused(t)    ) => OverUnder(t, s)
          case (Underused(s),    Underused(t)   ) => Underused(ev.combine(s, t))
          case (Underused(s),    OverUnder(t, u)) => OverUnder(t, ev.combine(s, u))
          case (OverUnder(s, t), Overused(u)    ) => OverUnder(ev.combine(s, u), t)
          case (OverUnder(s, t), Underused(u)   ) => OverUnder(s, ev.combine(t, u))
          case (OverUnder(s, t), OverUnder(u, v)) => OverUnder(ev.combine(s, u), ev.combine(t, v))
        }
    }

    object LinearityViolation {
      case class Overused[VarSet](vars: VarSet) extends LinearityViolation[VarSet]

      case class Underused[VarSet](vars: VarSet) extends LinearityViolation[VarSet]

      case class OverUnder[VarSet](overused: VarSet, underused: VarSet) extends LinearityViolation[VarSet]
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

    def combineLinear(l: LE, r: LE): LE

    def undefinedVars(vs: VarSet): E

    def fromLinearityViolation(e: LE): E
  }

  object ErrorFactory {
    given canonicalInstance[VarSet: Semigroup]: ErrorFactory[Error[VarSet], LinearityViolation[VarSet], VarSet] with {
      override def overusedVars(vs: VarSet): LinearityViolation[VarSet] = LinearityViolation.Overused(vs)
      override def underusedVars(vs: VarSet): LinearityViolation[VarSet] = LinearityViolation.Underused(vs)
      override def combineLinear(l: LinearityViolation[VarSet], r: LinearityViolation[VarSet]): LinearityViolation[VarSet] = l combine r
      override def undefinedVars(vs: VarSet): Error[VarSet] = Error.Undefined(vs)
      override def fromLinearityViolation(e: LinearityViolation[VarSet]): Error[VarSet] = e
    }
  }

  sealed trait Abstracted[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B] {
    import Abstracted._

    def mapExpr[Exp2[_]](g: [X] => Exp[X] => Exp2[X]): Abstracted[Exp2, |*|, AbsFun, LE, A, B] =
      this match {
        case Exact(f)             => Exact(f)
        case Closure(captured, f) => Closure(captured.trans(g), f)
        case Failure(e)           => Failure(e)
      }
  }

  object Abstracted {
    case class Exact[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B](
      f: AbsFun[A, B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class Closure[Exp[_], |*|[_, _], AbsFun[_, _], LE, X, A, B](
      captured: Tupled[|*|, Exp, X],
      f: AbsFun[X |*| A, B],
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]

    case class Failure[Exp[_], |*|[_, _], AbsFun[_, _], LE, A, B](
      e: LE,
    ) extends Abstracted[Exp, |*|, AbsFun, LE, A, B]
  }
}
