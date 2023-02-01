package libretto.lambda

import libretto.lambda.Lambdas.Error.LinearityViolation
import libretto.util.{Applicative, BiInjective, Exists, Semigroup, UniqueTypeArg}
import scala.annotation.targetName

trait Lambdas[-⚬[_, _], |*|[_, _], V, E, LE] {
  import Lambdas.ErrorFactory

  final type Tupled[F[_], A] = libretto.lambda.Tupled[|*|, F, A]

  final type Vars[A] = Tupled[Var[V, *], A]

  object Vars {
    def single[A](a: Var[V, A]): Vars[A] =
      Tupled.atom(a)

    def bi[A, B](a: Var[V, A], b: Var[V, B]): Vars[A |*| B] =
      zip(single(a), single(b))

    def zip[A, B](a: Vars[A], b: Vars[B]): Vars[A |*| B] =
      Tupled.zip(a, b)
  }

  type Expr[A]
  val Expr: Exprs

  trait Exprs {
    def variable[A](a: Var[V, A]): Expr[A]
    def map[A, B](e: Expr[A], f: A -⚬ B, resultVar: V)(using Context): Expr[B]
    def zip[A, B](a: Expr[A], b: Expr[B], resultVar: V)(using Context): Expr[A |*| B]
    def unzip[A, B](ab: Expr[A |*| B])(varName1: V, varName2: V)(using Context): (Expr[A], Expr[B])

    // XXX
    private[lambda] def unzip0[A, B](ab: Expr[A |*| B])(resultVar1: Var[V, A], resultVar2: Var[V, B]): (Expr[A], Expr[B])

    def resultVar[A](a: Expr[A]): Var[V, A]
  }

  extension [A](a: Expr[A]) {
    @targetName("exprMap")
    def map[B](f: A -⚬ B)(resultVar: V)(using Context): Expr[B] =
      Expr.map(a, f, resultVar)

    @targetName("exprZip")
    def zip[B](b: Expr[B])(resultVar: V)(using Context): Expr[A |*| B] =
      Expr.zip(a, b, resultVar)

    @targetName("exprResultVar")
    def resultVar: Var[V, A] =
      Expr.resultVar(a)
  }

  given UniqueTypeArg[Expr] with {
    override def testEqual[A, B](a: Expr[A], b: Expr[B]): Option[A =:= B] =
      summon[UniqueTypeArg[Var[V, *]]].testEqual(a.resultVar, b.resultVar)
  }

  type Context
  val Context: Contexts

  trait Contexts {
    def fresh(): Context

    def nested(parent: Context): Context

    def newVar[A](label: V)(using Context): Var[V, A]

    def registerNonLinearOps[A](v: Var[V, A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(using
      Context
    ): Unit

    def getSplit[A](v: Var[V, A])(using Context): Option[A -⚬ (A |*| A)]

    def getDiscard[A](v: Var[V, A])(using Context): Option[[B] => Unit => (A |*| B) -⚬ B]
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
  type AbsRes[A, B]     = Lambdas.Abstracted[Expr, |*|, -⚬,          LE, A, B]

  protected def eliminateVariable[A, B](
    boundVar: Var[V, A],
    expr: Expr[B],
  )(using Context): Abstracted[A, B]

  private def abs[A, B](
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using Context): Abstracted[A, B] = {
    val bindVar = Context.newVar[A](varName)
    eliminateVariable(bindVar, f(Expr.variable(bindVar)))
  }

  def absTopLevel[A, B](
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  ): Abstracted[A, B] =
    abs(varName, f)(using Context.fresh())

  def absNested[A, B](
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using parent: Context): Abstracted[A, B] =
    abs(varName, f)(using Context.nested(parent = parent))

  type VFun[A, B] = (V, Context ?=> Expr[A] => Expr[B])

  def switch[<+>[_, _], A, B](
    cases: Sink[VFun, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    Context,
  ): AbsRes[A, B]

  protected def switchImpl[<+>[_, _], A, B](
    cases: Sink[VFun, <+>, A, B],
    sum: [X, Y] => (X -⚬ B, Y -⚬ B) => (X <+> Y) -⚬ B,
    distribute: [X, Y, Z] => Unit => (X |*| (Y <+> Z)) -⚬ ((X |*| Y) <+> (X |*| Z))
  )(using
    BiInjective[|*|],
    SymmetricSemigroupalCategory[-⚬, |*|],
    ErrorFactory[E, LE, V],
    Context,
  ): AbsRes[A, B] = {
    val cases1: Sink[AbsRes, <+>, A, B] =
      cases.map[AbsRes] { [X] => (vf: VFun[X, B]) =>
        absNested(vf._1, vf._2)
          .mapFun([X] => (f: AbstractFun[X, B]) => f.fold)
      }

    cases1.reduce(
      [x, y] => (f1: AbsRes[x, B], f2: AbsRes[y, B]) => {
        import Lambdas.Abstracted.{Closure, Exact, Failure}
        (f1, f2) match {
          case (Exact(f1), Exact(f2)) =>
            Exact(sum(f1, f2))
          case (Closure(x, f1), Exact(f2)) =>
            discarderOf(x) match
              case Right(discardFst) => Closure(x, distribute(()) > sum(f1, discardFst(()) > f2))
              case Left(unusedVars)  => Failure(ErrorFactory.underusedVars(unusedVars))
          case (Exact(f1), Closure(y, f2)) =>
            discarderOf(y) match
              case Right(discardFst) => Closure(y, distribute(()) > sum(discardFst(()) > f1, f2))
              case Left(unusedVars)  => Failure(ErrorFactory.underusedVars(unusedVars))
          case (Closure(x, f1), Closure(y, f2)) =>
            product(x, y) match
              case LinCheck.Success(Exists.Some((p, p1, p2))) =>
                Closure(p, distribute(()) > sum(p1.inFst > f1, p2.inFst > f2))
              case LinCheck.Failure(e) =>
                Failure(e)
          case (Failure(e1), Failure(e2)) =>
            Failure(ErrorFactory.combineLinear(e1, e2))
          case (Failure(e1), _) =>
            Failure(e1)
          case (_, Failure(e2)) =>
            Failure(e2)
        }
      }
    )
  }

  private def discarderOf[A](a: Tupled[Expr, A])(using Context): Either[Var.Set[V], [B] => Unit => (A |*| B) -⚬ B] =
    ???

  private def product[A, B](
    a: Tupled[Expr, A],
    b: Tupled[Expr, B],
  )(using
    Context,
    BiInjective[|*|],
    SymmetricSemigroupalCategory[-⚬, |*|],
    ErrorFactory[E, LE, V],
  ): LinCheck[Exists[[P] =>> (Tupled[Expr, P], P -⚬ A, P -⚬ B)]] = {
    type LinChecked[X, Y] = LinCheck[X -⚬ Y]
    given shuffled: Shuffled[LinChecked, |*|] = Shuffled[LinChecked, |*|]
    given Shuffled.With[-⚬, |*|, shuffled.shuffle.type] = Shuffled[-⚬, |*|](shuffled.shuffle)

    val discardFst: [X, Y] => Expr[X] => LinChecked[X |*| Y, Y] =
      [X, Y] => (x: Expr[X]) =>
        Context.getDiscard(x.resultVar) match {
          case Some(discardFst) => LinCheck.Success(discardFst[Y](()))
          case None             => LinCheck.Failure(ErrorFactory.underusedVars(Var.Set(x.resultVar)))
        }

    (a product b)(discardFst) match
      case Exists.Some((p, p1, p2)) =>
        Applicative[LinCheck].map2(
          p1.traverse[LinCheck, -⚬]([x, y] => (f: LinChecked[x, y]) => f),
          p2.traverse[LinCheck, -⚬]([x, y] => (f: LinChecked[x, y]) => f),
        ) { (p1, p2) =>
          Exists((p, p1.fold, p2.fold))
        }
  }

  enum LinCheck[A] {
    case Success(value: A)
    case Failure(e: LE)
  }

  object LinCheck {
    given (using ErrorFactory[E, LE, V]): Applicative[LinCheck] with {
      override def pure[A](a: A): LinCheck[A] =
        Success(a)

      override def ap[A, B](ff: LinCheck[A => B])(fa: LinCheck[A]): LinCheck[B] =
        (ff, fa) match {
          case (Success(f), Success(a)) => Success(f(a))
          case (Success(_), Failure(e)) => Failure(e)
          case (Failure(e), Success(_)) => Failure(e)
          case (Failure(e), Failure(f)) => Failure(ErrorFactory.combineLinear(e, f))
        }
    }
  }
}

object Lambdas {
  def apply[-⚬[_, _], |*|[_, _], VarLabel, E, LE](using
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
    errors: ErrorFactory[E, LE, VarLabel],
  ): Lambdas[-⚬, |*|, VarLabel, E, LE] =
    new LambdasImpl[-⚬, |*|, VarLabel, E, LE]

  sealed trait Error[VarLabel]
  object Error {
    case class Undefined[VarLabel](vars: Var.Set[VarLabel]) extends Error[VarLabel]

    sealed trait LinearityViolation[VarLabel] extends Error[VarLabel] {
      import LinearityViolation._

      def combine(that: LinearityViolation[VarLabel]): LinearityViolation[VarLabel] =
        (this, that) match {
          case (Overused(s),     Overused(t)    ) => Overused(s merge t)
          case (Overused(s),     Underused(t)   ) => OverUnder(s, t)
          case (Overused(s),     OverUnder(t, u)) => OverUnder(s merge t, u)
          case (Underused(s),    Overused(t)    ) => OverUnder(t, s)
          case (Underused(s),    Underused(t)   ) => Underused(s merge t)
          case (Underused(s),    OverUnder(t, u)) => OverUnder(t, s merge u)
          case (OverUnder(s, t), Overused(u)    ) => OverUnder(s merge u, t)
          case (OverUnder(s, t), Underused(u)   ) => OverUnder(s, t merge u)
          case (OverUnder(s, t), OverUnder(u, v)) => OverUnder(s merge u, t merge v)
        }
    }

    object LinearityViolation {
      case class Overused[VarLabel](vars: Var.Set[VarLabel]) extends LinearityViolation[VarLabel]

      case class Underused[VarLabel](vars: Var.Set[VarLabel]) extends LinearityViolation[VarLabel]

      case class OverUnder[VarLabel](overused: Var.Set[VarLabel], underused: Var.Set[VarLabel]) extends LinearityViolation[VarLabel]
    }

    def overusedVar[L, A](v: Var[L, A]): LinearityViolation[L] =
      LinearityViolation.Overused(Var.Set(v))

    def underusedVar[L, A](v: Var[L, A]): LinearityViolation[L] =
      LinearityViolation.Underused(Var.Set(v))

    def undefinedVar[L, A](v: Var[L, A]): Error[L] =
      Undefined(Var.Set(v))
  }

  trait ErrorFactory[E, LE, VarLabel] {
    def underusedVars(vs: Var.Set[VarLabel]): LE
    def overusedVars(vs: Var.Set[VarLabel]): LE

    def combineLinear(l: LE, r: LE): LE

    def undefinedVars(vs: Var.Set[VarLabel]): E

    def fromLinearityViolation(e: LE): E
  }

  object ErrorFactory {
    def underusedVars[E, LE, VarLabel](using ef: ErrorFactory[E, LE, VarLabel])(vs: Var.Set[VarLabel]): LE = ef.underusedVars(vs)
    def overusedVars[E, LE, VarLabel](using ef: ErrorFactory[E, LE, VarLabel])(vs: Var.Set[VarLabel]): LE = ef.overusedVars(vs)
    def combineLinear[E, LE, VarLabel](using ef: ErrorFactory[E, LE, VarLabel])(l: LE, r: LE): LE = ef.combineLinear(l, r)
    def undefinedVars[E, LE, VarLabel](using ef: ErrorFactory[E, LE, VarLabel])(vs: Var.Set[VarLabel]): E = ef.undefinedVars(vs)
    def fromLinearityViolation[E, LE, VarLabel](using ef: ErrorFactory[E, LE, VarLabel])(e: LE): E = ef.fromLinearityViolation(e)

    given canonicalInstance[VarLabel]: ErrorFactory[Error[VarLabel], LinearityViolation[VarLabel], VarLabel] with {
      override def overusedVars(vs: Var.Set[VarLabel]): LinearityViolation[VarLabel] = LinearityViolation.Overused(vs)
      override def underusedVars(vs: Var.Set[VarLabel]): LinearityViolation[VarLabel] = LinearityViolation.Underused(vs)
      override def combineLinear(l: LinearityViolation[VarLabel], r: LinearityViolation[VarLabel]): LinearityViolation[VarLabel] = l combine r
      override def undefinedVars(vs: Var.Set[VarLabel]): Error[VarLabel] = Error.Undefined(vs)
      override def fromLinearityViolation(e: LinearityViolation[VarLabel]): Error[VarLabel] = e
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

    def mapFun[->[_, _]](g: [X] => AbsFun[X, B] => (X -> B)): Abstracted[Exp, |*|, ->, LE, A, B] =
      this match {
        case Exact(f)      => Exact(g(f))
        case Closure(x, f) => Closure(x, g(f))
        case Failure(e)    => Failure(e)
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
