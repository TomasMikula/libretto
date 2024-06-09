package libretto.lambda

import libretto.lambda.Lambdas.LinearityViolation
import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, UniqueTypeArg, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import scala.annotation.targetName

/**
  * @tparam V information associated with variables
  * @tparam C information associated with lambda contexts (scopes)
  */
trait Lambdas[-⚬[_, _], |*|[_, _], V, C] {
  final type Tupled[F[_], A] = libretto.lambda.Tupled[|*|, F, A]

  type Expr[A]
  val Expr: Exprs

  trait Exprs {
    def variable[A](a: Var[V, A]): Expr[A]
    def map[A, B](e: Expr[A], f: A -⚬ B)(resultVarName: V)(using Context): Expr[B]
    def zip[A, B](a: Expr[A], b: Expr[B])(resultVarName: V)(using Context): Expr[A |*| B]
    def zipN[A](a: Tupled[Expr, A])(resultVarName: V)(using Context): Expr[A]
    def unzip[A, B](ab: Expr[A |*| B])(varName1: V, varName2: V)(using Context): (Expr[A], Expr[B])
    def const[A](introduce: [x] => Unit => x -⚬ (A |*| x))(varName: V)(using Context): Expr[A]

    def resultVar[A](a: Expr[A]): Var[V, A]
    def initialVars[A](a: Expr[A]): Var.Set[V]

    def initialVars[A](as: Tupled[Expr, A]): Var.Set[V] =
      as.foldMap0([x] => (x: Expr[x]) => initialVars(x), _ merge _)
  }

  extension [A](a: Expr[A]) {
    @targetName("exprMap")
    infix def map[B](f: A -⚬ B)(resultVar: V)(using Context): Expr[B] =
      Expr.map(a, f)(resultVar)

    @targetName("exprZip")
    infix def zip[B](b: Expr[B])(resultVar: V)(using Context): Expr[A |*| B] =
      Expr.zip(a, b)(resultVar)

    @targetName("exprResultVar")
    def resultVar: Var[V, A] =
      Expr.resultVar(a)
  }

  given UniqueTypeArg[Expr] with {
    override def testEqual[A, B](a: Expr[A], b: Expr[B]): Option[A =:= B] =
      summon[UniqueTypeArg[Var[V, _]]].testEqual(a.resultVar, b.resultVar)
  }

  type Context
  val Context: Contexts

  trait Contexts {
    def fresh(info: C): Context

    def nested(info: C, parent: Context): Context

    def info(using ctx: Context): C

    def newVar[A](label: V)(using Context): Var[V, A]

    def isDefiningFor[A](v: Var[V, A])(using ctx: Context): Boolean

    def registerNonLinearOps[A](a: Expr[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[[B] => Unit => (A |*| B) -⚬ B],
    )(using
      Context
    ): Unit

    def registerConstant[A](v: Var[V, A])(
      introduce: [x] => Unit => x -⚬ (A |*| x),
    )(using ctx: Context): Unit

    def getSplit[A](v: Var[V, A])(using Context): Option[A -⚬ (A |*| A)]

    def getDiscard[A](v: Var[V, A])(using Context): Option[[B] => Unit => (A |*| B) -⚬ B]

    def getConstant[A](v: Var[V, A])(using Context): Option[[x] => Unit => x -⚬ (A |*| x)]

    def registerSplit[A](a: Expr[A])(split: A -⚬ (A |*| A))(using Context): Unit =
      registerNonLinearOps(a)(Some(split), None)

    def registerDiscard[A](a: Expr[A])(discard: [B] => Unit => (A |*| B) -⚬ B)(using Context): Unit =
      registerNonLinearOps(a)(None, Some(discard))
  }

  type DelambdifiedSuccess[A, B] = libretto.lambda.CapturingFun[-⚬, |*|, Tupled[Expr, _], A, B]
  type Delambdified[A, B] = Validated[LinearityViolation[V, C], DelambdifiedSuccess[A, B]]

  protected def eliminateLocalVariables[A, B](
    boundVar: Var[V, A],
    expr: Expr[B],
  )(using Context): Delambdified[A, B]

  private def delambdify[A, B](
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using Context): Delambdified[A, B] = {
    val bindVar = Context.newVar[A](varName)
    eliminateLocalVariables(bindVar, f(Expr.variable(bindVar)))
  }

  def delambdifyTopLevel[A, B](
    freshCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  ): Delambdified[A, B] =
    delambdify(varName, f)(using Context.fresh(freshCtxInfo))

  def delambdifyNested[A, B](
    nestedCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using parent: Context): Delambdified[A, B] =
    delambdify(varName, f)(using Context.nested(nestedCtxInfo, parent = parent))

  def switch[<+>[_, _], A, B](
    cases: Sink[DelambdifiedSuccess, <+>, A, B],
  )(using
    CocartesianSemigroupalCategory[-⚬, <+>],
    Distribution[-⚬, |*|, <+>],
    Context,
  ): Validated[
    LinearityViolation[V, C],
    DelambdifiedSuccess[A, B]
  ]

  protected def switchImpl[<+>[_, _], A, B](
    cases: Sink[DelambdifiedSuccess, <+>, A, B],
  )(using
    BiInjective[|*|],
    SymmetricSemigroupalCategory[-⚬, |*|],
    CocartesianSemigroupalCategory[-⚬, <+>],
    Distribution[-⚬, |*|, <+>],
    Context,
  ): Validated[
    LinearityViolation[V, C],
    DelambdifiedSuccess[A, B]
  ] =
    CapturingFun.compileSink(cases)(getDiscarder, [X, Y] => union(_, _))

  def leastCommonCapture[A, B](
    f: CapturingFun[-⚬, |*|, Tupled[Expr, _], A, B],
    g: CapturingFun[-⚬, |*|, Tupled[Expr, _], A, B],
  )(using
    ctx: Context,
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Validated[
    LinearityViolation[V, C],
    CapturingFun[[a, b] =>> (a -⚬ b, a -⚬ b), |*|, Tupled[Expr, _], A, B]
  ] =
    CapturingFun.leastCommonCapture(f, g)(getDiscarder, [X, Y] => union(_, _))

  def leastCommonCapture[A, B](
    fs: NonEmptyList[CapturingFun[-⚬, |*|, Tupled[Expr, _], A, B]],
  )(using
    ctx: Context,
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Validated[
    LinearityViolation[V, C],
    CapturingFun[[a, b] =>> NonEmptyList[a -⚬ b], |*|, Tupled[Expr, _], A, B]
  ] =
    CapturingFun.leastCommonCapture(fs)(getDiscarder, [X, Y] => union(_, _))

  private def getDiscarder(using
    ctx: Context,
    cat: SemigroupalCategory[-⚬, |*|],
  ): [X] => Tupled[Expr, X] => Validated[LinearityViolation[V, C], [Y] => Unit => (X |*| Y) -⚬ Y] =
    [X] => (fx: Tupled[Expr, X]) => discarderOf(fx) match {
      case Right(discardFst) => Valid(discardFst)
      case Left(unusedVars)  => invalid(LinearityViolation.UnusedInBranch(unusedVars))
    }

  private def discarderOf[A](a: Tupled[Expr, A])(using
    ctx: Context,
    cat: SemigroupalCategory[-⚬, |*|],
  ): Either[Var.Set[V], [B] => Unit => (A |*| B) -⚬ B] =
    a.asBin match {
      case Bin.Leaf(x) =>
        val v = x.resultVar
        Context.getDiscard(v) match
          case Some(discardFst) => Right(discardFst)
          case None             => Left(Var.Set(v))
      case Bin.Branch(l, r) =>
        (discarderOf(Tupled.fromBin(l)), discarderOf(Tupled.fromBin(r))) match
          case (Right(f), Right(g)) => Right([B] => (_: Unit) => cat.fst(f(())) > g[B](()))
          case (Right(_), Left(ws)) => Left(ws)
          case (Left(vs), Right(_)) => Left(vs)
          case (Left(vs), Left(ws)) => Left(vs merge ws)
    }

  private def union[A, B](
    a: Tupled[Expr, A],
    b: Tupled[Expr, B],
  )(using
    Context,
    BiInjective[|*|],
    SymmetricSemigroupalCategory[-⚬, |*|],
  ): Validated[
    LinearityViolation[V, C],
    Exists[[P] =>> (Tupled[Expr, P], P -⚬ A, P -⚬ B)]
  ] = {
    type LinCheck[A] = Validated[LinearityViolation[V, C], A]
    type LinChecked[X, Y] = LinCheck[X -⚬ Y]
    given shuffled: Shuffled[LinChecked, |*|] = Shuffled[LinChecked, |*|]
    given Shuffled.With[-⚬, |*|, shuffled.shuffle.type] = Shuffled[-⚬, |*|](shuffled.shuffle)

    val discardFst: [X, Y] => Expr[X] => LinChecked[X |*| Y, Y] =
      [X, Y] => (x: Expr[X]) =>
        Context.getDiscard(x.resultVar) match {
          case Some(discardFst) => Valid(discardFst[Y](()))
          case None             => invalid(LinearityViolation.unusedInBranch(x.resultVar))
        }

    (a union b)(discardFst) match
      case Exists.Some((p, p1, p2)) =>
        Applicative[LinCheck].map2(
          p1.traverse[LinCheck, -⚬]([x, y] => (f: LinChecked[x, y]) => f),
          p2.traverse[LinCheck, -⚬]([x, y] => (f: LinChecked[x, y]) => f),
        ) { (p1, p2) =>
          Exists((p, p1.fold, p2.fold))
        }
  }
}

object Lambdas {
  def apply[-⚬[_, _], |*|[_, _], VarLabel, CtxLabel](
    universalSplit  : Option[[X]    => Unit => X -⚬ (X |*| X)] = None,
    universalDiscard: Option[[X, Y] => Unit => (X |*| Y) -⚬ Y] = None,
  )(using
    ssc: SymmetricSemigroupalCategory[-⚬, |*|],
    inj: BiInjective[|*|],
  ): Lambdas[-⚬, |*|, VarLabel, CtxLabel] =
    new LambdasImpl[-⚬, |*|, VarLabel, CtxLabel](
      universalSplit,
      universalDiscard,
    )

  enum LinearityViolation[VarLabel, CtxLabel]:
    case Overused(vars: Var.Set[VarLabel])
    case Unused(v: Var[VarLabel, ?], exitedCtx: CtxLabel)
    case UnusedInBranch(vars: Var.Set[VarLabel])

  object LinearityViolation {
    def overusedVar[V, C, A](v: Var[V, A]): LinearityViolation[V, C] =
      Overused(Var.Set(v))

    def unusedVar[V, C, A](v: Var[V, A], exitedCtx: C): LinearityViolation[V, C] =
      Unused(v, exitedCtx)

    def unusedInBranch[V, C, A](v: Var[V, A]): LinearityViolation[V, C] =
      UnusedInBranch(Var.Set(v))
  }
}
