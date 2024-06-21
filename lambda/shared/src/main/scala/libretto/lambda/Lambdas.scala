package libretto.lambda

import libretto.lambda.Lambdas.LinearityViolation
import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, UniqueTypeArg, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import scala.annotation.targetName

/**
  * @tparam V information associated with variables
  * @tparam C information associated with lambda contexts (scopes)
  */
trait Lambdas[->[_, _], **[_, _], V, C] {
  val shuffled: Shuffled[->, **]
  import shuffled.{Shuffled as ~>}

  final type Tupled[F[_], A] = libretto.lambda.Tupled[**, F, A]

  type Expr[A]
  val Expr: Exprs

  trait Exprs {
    def variable[A](a: Var[V, A]): Expr[A]
    def map[A, B](e: Expr[A], f: A -> B)(resultVarName: V)(using Context): Expr[B]
    def zip[A, B](a: Expr[A], b: Expr[B])(resultVarName: V)(using Context): Expr[A ** B]
    def zipN[A](a: Tupled[Expr, A])(resultVarName: V)(using Context): Expr[A]
    def unzip[A, B](ab: Expr[A ** B])(varName1: V, varName2: V)(using Context): (Expr[A], Expr[B])
    def const[A](introduce: [x] => Unit => x -> (A ** x))(varName: V)(using Context): Expr[A]

    def resultVar[A](a: Expr[A]): Var[V, A]
    def initialVars[A](a: Expr[A]): Var.Set[V]

    def initialVars[A](as: Tupled[Expr, A]): Var.Set[V] =
      as.foldMap0([x] => (x: Expr[x]) => initialVars(x), _ merge _)
  }

  extension [A](a: Expr[A]) {
    @targetName("exprMap")
    infix def map[B](f: A -> B)(resultVar: V)(using Context): Expr[B] =
      Expr.map(a, f)(resultVar)

    @targetName("exprZip")
    infix def zip[B](b: Expr[B])(resultVar: V)(using Context): Expr[A ** B] =
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
      split: Option[A -> (A ** A)],
      discard: Option[[B] => Unit => (A ** B) -> B],
    )(using
      Context
    ): Unit

    def registerConstant[A](v: Var[V, A])(
      introduce: [x] => Unit => x -> (A ** x),
    )(using ctx: Context): Unit

    def getSplit[A](v: Var[V, A])(using Context): Option[A -> (A ** A)]

    def getDiscard[A](v: Var[V, A])(using Context): Option[[B] => Unit => (A ** B) -> B]

    def getConstant[A](v: Var[V, A])(using Context): Option[[x] => Unit => x -> (A ** x)]

    def registerSplit[A](a: Expr[A])(split: A -> (A ** A))(using Context): Unit =
      registerNonLinearOps(a)(Some(split), None)

    def registerDiscard[A](a: Expr[A])(discard: [B] => Unit => (A ** B) -> B)(using Context): Unit =
      registerNonLinearOps(a)(None, Some(discard))
  }

  type LinearityViolation = Lambdas.LinearityViolation[V, C]
  type Delambdified[A, B] = CapturingFun[~>, **, Tupled[Expr, _], A, B]
  type Delambdifold[A, B] = CapturingFun[->, **, Tupled[Expr, _], A, B]

  private def delambdifold[A, B](f: Delambdified[A, B])(using SymmetricSemigroupalCategory[->, **]): Delambdifold[A, B] =
    f.mapFun[->]([X, Y] => (g: X ~> Y) => g.fold)

  protected def eliminateLocalVariables[A, B](
    boundVar: Var[V, A],
    expr: Expr[B],
  )(using
    Context,
  ): Validated[
    LinearityViolation,
    Delambdified[A, B]
  ]

  private def delambdify[A, B](
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using
    Context,
  ): Validated[
    LinearityViolation,
    Delambdified[A, B]
  ] = {
    val bindVar = Context.newVar[A](varName)
    eliminateLocalVariables(bindVar, f(Expr.variable(bindVar)))
  }

  def delambdifyTopLevel[A, B](
    freshCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  ): Validated[
    LinearityViolation,
    Delambdified[A, B]
  ] =
    delambdify(varName, f)(using Context.fresh(freshCtxInfo))

  def delambdifyFoldTopLevel[A, B](
    freshCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using
    SymmetricSemigroupalCategory[->, **],
  ): Validated[
    LinearityViolation,
    Delambdifold[A, B]
  ] =
    delambdifyTopLevel(freshCtxInfo, varName, f)
      .map(delambdifold)

  def delambdifyNested[A, B](
    nestedCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using
    parent: Context,
  ): Validated[
    LinearityViolation,
    Delambdified[A, B]
  ] =
    delambdify(varName, f)(using Context.nested(nestedCtxInfo, parent = parent))

  def delambdifyFoldNested[A, B](
    nestedCtxInfo: C,
    varName: V,
    f: Context ?=> Expr[A] => Expr[B],
  )(using
    parent: Context,
    cat: SymmetricSemigroupalCategory[->, **],
  ): Validated[
    LinearityViolation,
    Delambdifold[A, B]
  ] =
    delambdifyNested(nestedCtxInfo, varName, f)
      .map(delambdifold)

  def compoundDiscarder(using
    ctx: Context,
    cat: SymmetricSemigroupalCategory[->, **],
  ): [X] => Tupled[Expr, X] => Validated[LinearityViolation.UnusedInBranch[V, C], [Y] => Unit => (X ** Y) -> Y] =
    [X] => x => compoundDiscarderSh(x).map(f => [Y] => (u: Unit) => f[Y](u).fold)

  def compoundDiscarderSh(using
    ctx: Context,
  ): [X] => Tupled[Expr, X] => Validated[LinearityViolation.UnusedInBranch[V, C], [Y] => Unit => (X ** Y) ~> Y] =
    getDiscarder

  def exprUniter(using
    Context,
    BiInjective[**],
    SymmetricSemigroupalCategory[->, **],
  ): [A, B] => (
    Tupled[Expr, A],
    Tupled[Expr, B],
  ) => Validated[
    LinearityViolation.UnusedInBranch[V, C],
    Exists[[P] =>> (Tupled[Expr, P], P -> A, P -> B)]
  ] =
    [A, B] => (a, b) => exprUniterSh(a, b).map { case Exists.Some((p, p1, p2)) => Exists((p, p1.fold, p2.fold))}

  def exprUniterSh(using
    Context,
    BiInjective[**],
  ): [A, B] => (
    Tupled[Expr, A],
    Tupled[Expr, B],
  ) => Validated[
    LinearityViolation.UnusedInBranch[V, C],
    Exists[[P] =>> (Tupled[Expr, P], P ~> A, P ~> B)]
  ] =
    [A, B] => union(_, _)

  private def getDiscarder(using
    ctx: Context,
  ): [X] => Tupled[Expr, X] => Validated[LinearityViolation.UnusedInBranch[V, C], [Y] => Unit => (X ** Y) ~> Y] =
    [X] => (fx: Tupled[Expr, X]) => discarderOf(fx) match {
      case Right(discardFst) => Valid(discardFst)
      case Left(unusedVars)  => invalid(LinearityViolation.UnusedInBranch(unusedVars))
    }

  private def discarderOf[A](a: Tupled[Expr, A])(using
    ctx: Context,
  ): Either[Var.Set[V], [B] => Unit => (A ** B) ~> B] =
    a.asBin match {
      case Bin.Leaf(x) =>
        val v = x.resultVar
        Context.getDiscard(v) match
          case Some(discardFst) => Right(liftDiscarder(discardFst))
          case None             => Left(Var.Set(v))
      case Bin.Branch(l, r) =>
        (discarderOf(Tupled.fromBin(l)), discarderOf(Tupled.fromBin(r))) match
          case (Right(f), Right(g)) => Right([B] => (_: Unit) => f(()).inFst > g[B](()))
          case (Right(_), Left(ws)) => Left(ws)
          case (Left(vs), Right(_)) => Left(vs)
          case (Left(vs), Left(ws)) => Left(vs merge ws)
    }

  private def liftDiscarder[X](
    f: [Y] => Unit => (X ** Y) -> Y,
  ):   [Y] => Unit => (X ** Y) ~> Y =
    [Y] => (_: Unit) => shuffled.lift(f[Y](()))

  private def union[A, B](
    a: Tupled[Expr, A],
    b: Tupled[Expr, B],
  )(using
    Context,
    BiInjective[**],
  ): Validated[
    LinearityViolation.UnusedInBranch[V, C],
    Exists[[P] =>> (Tupled[Expr, P], P ~> A, P ~> B)]
  ] = {
    type LinCheck[A] = Validated[LinearityViolation.UnusedInBranch[V, C], A]
    type LinChecked[X, Y] = LinCheck[X -> Y]
    given shuffledA: Shuffled.With[LinChecked, **, shuffled.shuffle.type] = Shuffled[LinChecked, **](shuffled.shuffle)

    val discardFst: [X, Y] => Expr[X] => LinChecked[X ** Y, Y] =
      [X, Y] => (x: Expr[X]) =>
        Context.getDiscard(x.resultVar) match {
          case Some(discardFst) => Valid(discardFst[Y](()))
          case None             => invalid(LinearityViolation.unusedInBranch(x.resultVar))
        }

    (a union b)(discardFst) match
      case Exists.Some((p, p1, p2)) =>
        Applicative[LinCheck].map2(
          p1.traverse[LinCheck, ->]([x, y] => (f: LinChecked[x, y]) => f)(using shuffled),
          p2.traverse[LinCheck, ->]([x, y] => (f: LinChecked[x, y]) => f)(using shuffled),
        ) { (p1, p2) =>
          Exists((p, p1, p2))
        }
  }
}

object Lambdas {
  class LambdasFactory[->[_, _], **[_, _], SHUFFLED <: Shuffled[->, **]](sh: SHUFFLED) {
    def apply[VarLabel, CtxLabel](
      universalSplit  : Option[[X]    => Unit => X -> (X ** X)] = None,
      universalDiscard: Option[[X, Y] => Unit => (X ** Y) -> Y] = None,
    )(using
      inj: BiInjective[**],
    ): Lambdas[->, **, VarLabel, CtxLabel] { val shuffled: SHUFFLED } =
      new LambdasImpl[->, **, VarLabel, CtxLabel, sh.type](
        sh,
        universalSplit,
        universalDiscard,
      )
  }

  def using[->[_, _], **[_, _]](
    sh: Shuffled[->, **],
  ): LambdasFactory[->, **, sh.type] =
    LambdasFactory(sh)

  def apply[->[_, _], **[_, _], VarLabel, CtxLabel](
    universalSplit  : Option[[X]    => Unit => X -> (X ** X)] = None,
    universalDiscard: Option[[X, Y] => Unit => (X ** Y) -> Y] = None,
  )(using
    inj: BiInjective[**],
  ): Lambdas[->, **, VarLabel, CtxLabel] =
    using(Shuffled[->, **])(universalSplit, universalDiscard)

  enum LinearityViolation[VarLabel, CtxLabel]:
    case Overused(vars: Var.Set[VarLabel])
    case Unused(v: Var[VarLabel, ?], exitedCtx: CtxLabel)
    case UnusedInBranch(vars: Var.Set[VarLabel])

  object LinearityViolation {
    def overusedVar[V, C, A](v: Var[V, A]): LinearityViolation[V, C] =
      Overused(Var.Set(v))

    def unusedVar[V, C, A](v: Var[V, A], exitedCtx: C): LinearityViolation[V, C] =
      Unused(v, exitedCtx)

    def unusedInBranch[V, C, A](v: Var[V, A]): LinearityViolation.UnusedInBranch[V, C] =
      UnusedInBranch(Var.Set(v))
  }
}
