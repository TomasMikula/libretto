package libretto.lambda

import libretto.lambda.Lambdas.LinearityViolation
import libretto.lambda.util.{Applicative, BiInjective, ClampEq, Exists, NonEmptyList, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import scala.annotation.targetName

/**
  * @tparam V information associated with variables
  * @tparam C information associated with lambda contexts (scopes)
  */
trait Lambdas[->[_, _], **[_, _], V, C] {
  val shuffled: ShuffledModule[->, **]
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
    def const[A](
      introFst: [x] => DummyImplicit ?=> x -> (A ** x),
      introSnd: [x] => DummyImplicit ?=> x -> (x ** A),
    )(
      varName: V
    )(using
      Context
    ): Expr[A]

    def const[A](introFst: [x] => DummyImplicit ?=> x -> (A ** x))(varName: V)(using
      ctx: Context,
      cat: SymmetricSemigroupalCategory[->, **],
    ): Expr[A] =
      const(
        introFst,
        [x] => _ ?=> introFst[x] > cat.swap,
      )(varName)

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

  given ClampEq[Expr] with {
    override def testEqual[A, B](a: Expr[A], b: Expr[B]): Option[A =:= B] =
      summon[ClampEq[Var[V, _]]].testEqual(a.resultVar, b.resultVar)
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
      discard: Option[(
        [B] => DummyImplicit ?=> (A ** B) -> B,
        [B] => DummyImplicit ?=> (B ** A) -> B,
      )],
    )(using
      Context
    ): Unit

    def registerConstant[A](v: Var[V, A])(
      introFst: [x] => DummyImplicit ?=> x -> (A ** x),
      introSnd: [x] => DummyImplicit ?=> x -> (x ** A),
    )(using ctx: Context): Unit

    def getSplit[A](v: Var[V, A])(using Context): Option[A -> (A ** A)]

    def getDiscard[A](v: Var[V, A])(using Context): Option[(
      [B] => DummyImplicit ?=> (A ** B) -> B,
      [B] => DummyImplicit ?=> (B ** A) -> B,
    )]

    def getDiscardSh[A](v: Var[V, A])(using Context): Option[(
      [B] => DummyImplicit ?=> shuffled.Shuffled[A ** B, B],
      [B] => DummyImplicit ?=> shuffled.Shuffled[B ** A, B],
    )] =
      getDiscard(v).map { (discardFst, discardSnd) =>
        (
          [B] => (_: DummyImplicit) ?=> shuffled.lift(discardFst[B]),
          [B] => (_: DummyImplicit) ?=> shuffled.lift(discardSnd[B]),
        )
      }

    def exprDiscarders(using Context): [X] => Expr[X] => Option[(
      [Y] => DummyImplicit ?=> (X ** Y) -> Y,
      [Y] => DummyImplicit ?=> (Y ** X) -> Y,
    )] =
      [X] => x => getDiscard(x.resultVar)

    def exprDiscarderSh(using Context): [X] => Expr[X] => Option[(
      [Y] => DummyImplicit ?=> (X ** Y) ~> Y,
      [Y] => DummyImplicit ?=> (Y ** X) ~> Y,
    )] =
      [X] => x => getDiscardSh(x.resultVar)

    def getConstant[A](v: Var[V, A])(using Context): Option[(
      [x] => DummyImplicit ?=> x -> (A ** x), // introFst
      [x] => DummyImplicit ?=> x -> (x ** A), // introSnd
    )]

    def registerSplit[A](a: Expr[A])(split: A -> (A ** A))(using Context): Unit =
      registerNonLinearOps(a)(Some(split), None)

    def registerDiscard[A](a: Expr[A])(
      discardFst: [B] => DummyImplicit ?=> (A ** B) -> B,
      discardSnd: [B] => DummyImplicit ?=> (B ** A) -> B,
    )(using Context): Unit =
      registerNonLinearOps(a)(None, Some((discardFst, discardSnd)))
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
}

object Lambdas {
  class LambdasFactory[->[_, _], **[_, _], SHUFFLED <: ShuffledModule[->, **]](sh: SHUFFLED) {
    def apply[VarLabel, CtxLabel](
      universalSplit  : Option[[X]    => DummyImplicit ?=> X -> (X ** X)] = None,
      universalDiscard: Option[[X, Y] => DummyImplicit ?=> ((X ** Y) -> Y, (Y ** X) -> Y)] = None,
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
    sh: ShuffledModule[->, **],
  ): LambdasFactory[->, **, sh.type] =
    LambdasFactory(sh)

  def apply[->[_, _], **[_, _], VarLabel, CtxLabel](
    universalSplit  : Option[[X]    => DummyImplicit ?=> X -> (X ** X)] = None,
    universalDiscard: Option[[X, Y] => DummyImplicit ?=> ((X ** Y) -> Y, (Y ** X) -> Y)] = None,
  )(using
    inj: BiInjective[**],
  ): Lambdas[->, **, VarLabel, CtxLabel] =
    using(Shuffled[->, **])(universalSplit, universalDiscard)

  enum LinearityViolation[VarLabel, CtxLabel]:
    case Overused(vars: Var.Set[VarLabel], exitedCtx: CtxLabel)
    case Unused(v: Var[VarLabel, ?], exitedCtx: CtxLabel)

  object LinearityViolation {
    def overusedVar[V, C, A](v: Var[V, A], exitedCtx: C): LinearityViolation[V, C] =
      Overused(Var.Set(v), exitedCtx)

    def unusedVar[V, C, A](v: Var[V, A], exitedCtx: C): LinearityViolation[V, C] =
      Unused(v, exitedCtx)

  }
}
