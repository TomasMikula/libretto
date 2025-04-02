package libretto.scaletto.impl

import libretto.scaletto.Scaletto
import libretto.lambda.{AForest, CapturingFun, ClosedSymmetricMonoidalCategory, CocartesianSemigroupalCategory, CoproductPartitioning, Distribution, EnumModule, Focus, Lambdas, LambdasImpl, Member, Partitioning, PatternMatching, SemigroupalCategory, Shuffled, Sink, SymmetricSemigroupalCategory, Tupled, Var}
import libretto.lambda.Partitioning.SubFun
import libretto.lambda.util.{Applicative, Exists, NonEmptyList, SingletonType, SourcePos, Validated}
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import libretto.lambda.util.Monad.monadEither
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration
import scala.reflect.TypeTest

object FreeScaletto extends Scaletto {

  override type One = phantoms.One
  override type Void = phantoms.Void
  override type Done = phantoms.Done
  override type Need = phantoms.Need
  override type Ping = phantoms.Ping
  override type Pong = phantoms.Pong
  override type RTerminus = phantoms.RTerminus
  override type LTerminus = phantoms.LTerminus
  override type |*|[A, B] = phantoms.|*|[A, B]
  override type |+|[A, B] = phantoms.|+|[A, B]
  override type |&|[A, B] = phantoms.|&|[A, B]
  override type ||[A, B] = phantoms.||[A, B]
  override type ::[Label, T] = phantoms.::[Label, T]
  override type OneOf[Cases] = phantoms.OneOf[Cases]
  override type Rec[F[_]] = phantoms.Rec[F[_]]
  override type Sub[A, B] = phantoms.Sub[A, B]
  override type -[A] = phantoms.-[A]
  override type Val[A] = phantoms. Val[A]
  override type Res[A] = phantoms. Res[A]
  override type UInt31 = Val[Int]
  override type -⚬[A, B] = libretto.scaletto.impl.-⚬[A, B]

  import -⚬.{*, given}
  import Fun.*

  override type ScalaFun[A, B] = ScalaFunction[A, B]

  override object ScalaFun extends ScalaFuns {
    override def apply[A, B](f: A => B): ScalaFun[A, B]        = ScalaFunction.Direct(f)
    override def blocking[A, B](f: A => B): ScalaFun[A, B]     = ScalaFunction.Blocking(f)
    override def async[A, B](f: A => Async[B]): ScalaFun[A, B] = ScalaFunction.Asynchronous(f)

    override def adapt[A, B, Z, C](f: ScalaFun[A, B])(
      pre: Z => A,
      post: B => C,
    ): ScalaFun[Z, C] =
      f.adapt(pre, post)

    override def adaptWith[A, B, Z, P, C](f: ScalaFun[A, B])(
      pre: Z => (P, A),
      post: (P, B) => C,
    ): ScalaFun[Z, C] =
      f.adaptWith(pre, post)

    override def eval[A, B]: ScalaFun[(ScalaFun[A, B], A), B] =
      ScalaFunction.eval[A, B]
  }

  override def id[A]: A -⚬ A =
    -⚬.id[A]

  override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C =
    f > g

  override def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D) =
    -⚬.par(f, g)

  override def introFst[B]: B -⚬ (One |*| B) =
    -⚬.𝒞.introFst[B]

  override def introSnd[A]: A -⚬ (A |*| One) =
    -⚬.𝒞.introSnd[A]

  override def elimFst[B]: (One |*| B) -⚬ B =
    -⚬.𝒞.elimFst[B]

  override def elimSnd[A]: (A |*| One) -⚬ A =
    -⚬.𝒞.elimSnd[A]

  override def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C)) =
    -⚬.𝒞.assocLR

  override def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C) =
    -⚬.𝒞.assocRL

  override def swap[A, B]: (A |*| B) -⚬ (B |*| A) =
    -⚬.𝒞.swap

  override def injectL[A, B]: A -⚬ (A |+| B) =
    -⚬.cocat.injectL

  override def injectR[A, B]: B -⚬ (A |+| B) =
    -⚬.cocat.injectR

  override def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C =
    -⚬.cocat.either(f, g)

  override def absurd[A]: Void -⚬ A =
    Regular(Absurd())

  override def chooseL[A, B]: (A |&| B) -⚬ A =
    Regular(ChooseL())

  override def chooseR[A, B]: (A |&| B) -⚬ B =
    Regular(ChooseR())

  override def choice[A, B, C](f: A -⚬ B, g: A -⚬ C): A -⚬ (B |&| C) =
    -⚬.choice(f, g)

  override def ping: One -⚬ Ping =
    Regular(PingF())

  override def pong: Pong -⚬ One =
    Regular(PongF())

  override def delayIndefinitely: Done -⚬ RTerminus =
    Regular(DelayIndefinitely())

  override def regressInfinitely: LTerminus -⚬ Need =
    Regular(RegressInfinitely())

  override def fork: Done -⚬ (Done |*| Done) =
    Regular(Fork())

  override def join: (Done |*| Done) -⚬ Done =
    Regular(Join())

  override def forkNeed: (Need |*| Need) -⚬ Need =
    Regular(ForkNeed())

  override def joinNeed: Need -⚬ (Need |*| Need) =
    Regular(JoinNeed())

  override def notifyDoneL: Done -⚬ (Ping |*| Done) =
    Regular(NotifyDoneL())

  override def notifyNeedL: (Pong |*| Need) -⚬ Need =
    Regular(NotifyNeedL())

  override def forkPing: Ping -⚬ (Ping |*| Ping) =
    Regular(ForkPing())

  override def forkPong: (Pong |*| Pong) -⚬ Pong =
    Regular(ForkPong())

  override def joinPing: (Ping |*| Ping) -⚬ Ping =
    Regular(JoinPing())

  override def joinPong: Pong -⚬ (Pong |*| Pong) =
    Regular(JoinPong())

  override def strengthenPing: Ping -⚬ Done =
    Regular(StrengthenPing())

  override def strengthenPong: Need -⚬ Pong =
    Regular(StrengthenPong())

  override def joinRTermini: (RTerminus |*| RTerminus) -⚬ RTerminus =
    Regular(JoinRTermini())

  override def joinLTermini: LTerminus -⚬ (LTerminus |*| LTerminus) =
    Regular(JoinLTermini())

  override def notifyEither[A, B]: (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    Regular(NotifyEither())

  override def notifyChoice[A, B]: (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    Regular(NotifyChoice())

  override def injectLOnPing[A, B]: (Ping |*| A) -⚬ (A |+| B) =
    Regular(InjectLOnPing())

  override def chooseLOnPong[A, B]: (A |&| B) -⚬ (Pong |*| A) =
    Regular(ChooseLOnPong())

  override def distributeL[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
    Regular(DistributeL())

  override def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)) =
    Regular(CoDistributeL())

  override def rInvertSignal: (Done |*| Need) -⚬ One =
    Regular(RInvertSignal())

  override def lInvertSignal: One -⚬ (Need |*| Done) =
    Regular(LInvertSignal())

  override def rInvertPingPong: (Ping |*| Pong) -⚬ One =
    Regular(RInvertPingPong())

  override def lInvertPongPing: One -⚬ (Pong |*| Ping) =
    Regular(LInvertPongPing())

  override def rInvertTerminus: (RTerminus |*| LTerminus) -⚬ One =
    Regular(RInvertTerminus())

  override def lInvertTerminus: One -⚬ (LTerminus |*| RTerminus) =
    Regular(LInvertTerminus())

  override def rec[A, B](using pos: SourcePos)(f: (A -⚬ B) => (A -⚬ B)): A -⚬ B =
    -⚬.rec(pos, f)

  override def rec[A, B](f: (Sub[A, B] |*| A) -⚬ B): A -⚬ B =
    Regular(RecFun(f))

  override def invoke[A, B]: (Sub[A, B] |*| A) -⚬ B =
    Regular(InvokeSub())

  override def comonoidSub[A, B]: Comonoid[Sub[A, B]] =
    new Comonoid[Sub[A, B]]:
      override def counit: Sub[A, B] -⚬ One = -⚬.ignoreSub
      override def split: Sub[A, B] -⚬ (Sub[A, B] |*| Sub[A, B]) = -⚬.dupSub

  override def unpack[F[_]]: Rec[F] -⚬ F[Rec[F]] =
    Regular(Unpack())

  override def pack[F[_]]: F[Rec[F]] -⚬ Rec[F] =
    Regular(Pack())

  override def racePair: (Ping |*| Ping) -⚬ (One |+| One) =
    Regular(RacePair())

  override def selectPair: (One |&| One) -⚬ (Pong |*| Pong) =
    Regular(SelectPair())

  override def sharedCode[A, B](using pos: SourcePos)(f: A -⚬ B): A -⚬ B =
    f.blueprint match
      case Valid(f) =>
        FunRef(new Object, f) // XXX use a proper ID
      case Invalid(es) =>
        assemblyError(ForbiddenCaptureOfRecursiveCallsIntoLibCode(pos, es))

  override def sub[A, B](using pos: SourcePos)(f: A -⚬ B): One -⚬ Sub[A, B] =
    f.blueprint match
      case Valid(f) =>
        ConstSub(f)
      case Invalid(es) =>
        assemblyError(ForbiddenCaptureOfRecursiveCallsIntoLibCode(pos, es))

  override def crashWhenDone[A, B](msg: String): (Done |*| A) -⚬ B =
    Regular(CrashWhenDone(msg))

  override def delay: Val[FiniteDuration] -⚬ Done =
    Regular(Delay())

  override def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]) =
    Regular(LiftEither())

  override def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B]) =
    Regular(LiftPair())

  override def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)] =
    Regular(UnliftPair())

  override def mapVal[A, B](f: ScalaFun[A, B]): Val[A] -⚬ Val[B] =
    Regular(MapVal(f))

  override def constVal[A](a: A): Done -⚬ Val[A] =
    Regular(ConstVal(a))

  override def constNeg[A](a: A): Neg[A] -⚬ Need =
    Regular(ConstNeg(a))

  override def neglect[A]: Val[A] -⚬ Done =
    Regular(Neglect())

  override def notifyVal[A]: Val[A] -⚬ (Ping |*| Val[A]) =
    Regular(NotifyVal())

  override def notifyNeg[A]: (Pong |*| Neg[A]) -⚬ Neg[A] =
    Regular(NotifyNeg())

  override def debugPrint(msg: String): Ping -⚬ One =
    Regular(DebugPrint(msg))

  override def acquire[A, R, B](
    acquire: ScalaFun[A, (R, B)],
    release: Option[ScalaFun[R, Unit]],
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    Regular(Acquire(acquire, release))

  override def tryAcquire[A, R, B, E](
    acquire: ScalaFun[A, Either[E, (R, B)]],
    release: Option[ScalaFun[R, Unit]],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])) =
    Regular(TryAcquire(acquire, release))

  override def release[R]: Res[R] -⚬ Done =
    Regular(Release())

  override def releaseWith[R, A, B](f: ScalaFunction[(R, A), B]): (Res[R] |*| Val[A]) -⚬ Val[B] =
    Regular(ReleaseWith(f))

  override def effect[R, A, B](f: ScalaFunction[(R, A), B]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    Regular(Effect(f))

  override def effectWr[R, A](f: ScalaFunction[(R, A), Unit]): (Res[R] |*| Val[A]) -⚬ Res[R] =
    Regular(EffectWr(f))

  override def tryEffectAcquire[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| (Val[E] |+| (Res[S] |*| Val[B]))) =
    Regular(TryEffectAcquire(f, release))

  override def tryTransformResource[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    Regular(TryTransformResource(f, release))

  override def trySplitResource[R, A, S, T, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, T, B)]],
    release1: Option[ScalaFunction[S, Unit]],
    release2: Option[ScalaFunction[T, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])) =
    Regular(TrySplitResource(f, release1, release2))

  override def forevert[A]: One -⚬ (-[A] |*| A) =
    Regular(Forevert())

  override def backvert[A]: (A |*| -[A]) -⚬ One =
    Regular(Backvert())

  override def distributeInversion[A, B]: -[A |*| B] -⚬ (-[A] |*| -[B]) =
    Regular(DistributeInversion())

  override def factorOutInversion[A, B]: (-[A] |*| -[B]) -⚬ -[A |*| B] =
    Regular(FactorOutInversion())

  override def category: ClosedSymmetricMonoidalCategory[-⚬, |*|, One, =⚬] =
    𝒞

  override def sizeOf[A, B](f: A -⚬ B): Long =
    f.size

  override object UInt31 extends UInt31Scaletto {
    override def apply(n: Int): Done -⚬ UInt31 = {
      require(n >= 0, s"$n is negative")
      constVal(n)
    }

    override def add: (UInt31 |*| UInt31) -⚬ UInt31 =
      unliftPair > mapVal { case (x, y) => x + y }

    override def multiply: (UInt31 |*| UInt31) -⚬ UInt31 =
      unliftPair > mapVal { case (x, y) => x * y }

    override def increment: UInt31 -⚬ UInt31 =
      mapVal { _ + 1 }

    override def decrement: UInt31 -⚬ (Done |+| UInt31) =
      mapVal[Int, Either[Unit, Int]] {
        case 0 => Left(())
        case n => Right(n-1)
      } > liftEither > either(
        FreeScaletto.this.neglect > injectL,
        injectR,
      )

    override def neglect: UInt31 -⚬ Done =
      FreeScaletto.this.neglect

    override def fromInt: Val[Int] -⚬ UInt31 =
      id

    override def toInt: UInt31 -⚬ Val[Int] =
      id
  }

  override val OneOf: EnumModule[-⚬, |*|, OneOf, ||, ::] =
    EnumModule[-⚬, |*|, OneOf, ||, ::](using 𝒞, cocatN, distributionN)

  override val SumPartitioning =
    new CoproductPartitioning[-⚬, |*|, |+|]("InL", "InR")(using 𝒞, cocat, distribution)

  private val patmat =
    new PatternMatching[-⚬, |*|]

  import patmat.{Pattern, PatternMatchError}

  private type Var[A] = libretto.lambda.Var[VarOrigin, A]

  private type Extractor[A, B] =
    libretto.lambda.Extractor[-⚬, |*|, A, B]

  private val Extractor =
    libretto.lambda.Extractor

  private case class ExtractorOccurrence[A, B](
    ext: Extractor[A, B],
    pos: SourcePos,
  )

  private type PartialFun[A, B] =
    (A -⚬ B) | ExtractorOccurrence[A, B]

  private val psh: Shuffled[PartialFun, |*|] =
    Shuffled[PartialFun, |*|]

  private type -?>[A, B] = psh.Shuffled[A, B]

  private type LinearityViolation = Lambdas.LinearityViolation[VarOrigin, ScopeInfo]

  private def total[A, B](f: PartialFun[A, B]): TotalRes[A -⚬ B] =
    f match
      case g: (A -⚬ B) =>
        TotalRes.success(g)
      case p: ExtractorOccurrence[A, B] =>
        p.ext.isTotal match
          case Some(g) => TotalRes.success(g)
          case None => libretto.lambda.UnhandledCase.raise(s"Non-exhaustive matcher $p")

  private def foldTotal[A, B](f: A -?> B): TotalRes[A -⚬ B] =
    f.foldMapA(
      [X, Y] => (g: PartialFun[X, Y]) => total(g)
    )

  /** The result of extracting a total function from a partial one. */
  private type TotalRes[T] = Validated[(SourcePos, NonEmptyList[String]), T]
  private object TotalRes {
    def success[T](value: T): TotalRes[T] =
      Valid(value)
  }

  private val lambdas: Lambdas[PartialFun, |*|, VarOrigin, ScopeInfo] { val shuffled: psh.type } =
    Lambdas.using(psh)[VarOrigin, ScopeInfo]()

  override opaque type $[A] = lambdas.Expr[A]

  override opaque type LambdaContext = lambdas.Context

  private type MetaFun[A, B] = CapturingFun[-⚬, |*|, Tupled[|*|, $, _], A, B]

  override val `$`: $Ops = new $Ops {
    override def one(using pos: SourcePos, ctx: lambdas.Context): $[One] =
      lambdas.Expr.const([x] => _ ?=> introFst[x])(VarOrigin.OneIntro(pos))

    override def map[A, B](a: $[A])(f: A -⚬ B)(pos: SourcePos)(using
      lambdas.Context,
    ): $[B] =
      (a map f)(VarOrigin.FunAppRes(pos))

    override def zip[A, B](a: $[A], b: $[B])(
      pos: SourcePos,
    )(using
      lambdas.Context,
    ): $[A |*| B] =
      (a zip b)(VarOrigin.Pairing(pos))

    override def unzip[A, B](ab: $[A |*| B])(
      pos: SourcePos,
    )(using
      lambdas.Context,
    ): ($[A], $[B]) =
      lambdas.Expr.unzip(ab)(
        VarOrigin.Prj1(pos),
        VarOrigin.Prj2(pos),
      )

    override def matchAgainst[A, B](a: $[A], extractor: Extractor[A, B])(pos: SourcePos)(using LambdaContext): $[B] =
      lambdas.Expr.map(a, ExtractorOccurrence(extractor, pos))(VarOrigin.ExtractorRes(pos))

    override def app[A, B](f: $[A =⚬ B], a: $[A])(
      pos: SourcePos,
    )(using
      lambdas.Context,
    ): $[B] =
      map((f zip a)(VarOrigin.FunAndArg(pos)))(eval[A, B])(pos)

    override def nonLinear[A](a: $[A])(
      split: Option[A -⚬ (A |*| A)],
      discard: Option[A -⚬ One],
    )(
      pos: SourcePos,
    )(using
      lambdas.Context,
    ): $[A] = {
      lambdas.Context.registerNonLinearOps(a)(
        split,
        discard.map(f => (
          [B] => (_: DummyImplicit) ?=> elimFst[A, B](f),
          [B] => (_: DummyImplicit) ?=> elimSnd[B, A](f),
        )),
      )
      a
    }
  }

  private sealed trait UnpackOnlyFun[A, B]:
    def compile: (A -⚬ B)
    def reverseCompile: (B -⚬ A)

  private object UnpackOnlyFun {
    case class Unpack[F[_]]() extends UnpackOnlyFun[Rec[F], F[Rec[F]]]:
      override def compile: Rec[F] -⚬ F[Rec[F]] = unpack
      override def reverseCompile: F[Rec[F]] -⚬ Rec[F] = pack

    object UnpackOnlySubFun extends Partitioning.SubFun[-⚬, UnpackOnlyFun] {
      override def compile[X, Y](f: UnpackOnlyFun[X, Y]): X -⚬ Y = f.compile
      override def reverseCompile[X, Y](f: UnpackOnlyFun[X, Y]): Y -⚬ X = f.reverseCompile

      override def sameAs[G[_,_]](that: SubFun[-⚬, G]): Option[[X, Y] => UnpackOnlyFun[X, Y] => G[X, Y]] =
        that match
          case UnpackOnlySubFun =>
            Some([X, Y] => (f: UnpackOnlyFun[X, Y]) => f)
          case _ =>
            None

      override def testEqual[X, Y, Z](f: UnpackOnlyFun[X, Y], g: UnpackOnlyFun[X, Z]): Option[Y =:= Z] =
        (f, g) match
          case (Unpack(), Unpack()) =>
            Some(summon[Y =:= Z])
    }

    given Partitioning.SubFun[-⚬, UnpackOnlyFun] = UnpackOnlySubFun
  }

  override def recPartitioning[F[_]](
    p: Partitioning[-⚬, |*|, F[Rec[F]]],
  ): Partitioning[-⚬, |*|, Rec[F]] { type Partition[P] = p.Partition[P] } =
    p.contramap[UnpackOnlyFun, Rec[F]](
      UnpackOnlyFun.Unpack[F]()
    )

  private given SymmetricSemigroupalCategory[PartialFun, |*|] with {
    override def id[A]: PartialFun[A, A] = FreeScaletto.id
    override def assocLR[A, B, C]: PartialFun[(A |*| B) |*| C, A |*| (B |*| C)] = FreeScaletto.this.assocLR
    override def assocRL[A, B, C]: PartialFun[A |*| (B |*| C), (A |*| B) |*| C] = FreeScaletto.this.assocRL
    override def swap[A, B]: PartialFun[A |*| B, B |*| A] = FreeScaletto.this.swap
    override def andThen[A, B, C](f: PartialFun[A, B], g: PartialFun[B, C]): PartialFun[A, C] =
      (total(f) zip total(g)) match
        case Valid((f, g)) => FreeScaletto.this.andThen(f, g)
        case Invalid(es) => raiseTotalityViolations(es) // XXX
    override def par[A1, A2, B1, B2](f1: PartialFun[A1, B1], f2: PartialFun[A2, B2]): PartialFun[A1 |*| A2, B1 |*| B2] =
      (total(f1) zip total(f2)) match
        case Valid((f1, f2)) => FreeScaletto.this.par(f1, f2)
        case Invalid(es) => raiseTotalityViolations(es) // XXX
  }

  private type UnusedInBranch = PatternMatching.UnusedInBranch[VarOrigin, ScopeInfo]

  private def switchSink[A, R](
    a: $[A],
    cases: Sink[[x, y] =>> (ScopeInfo, lambdas.Delambdifold[x, y]), |+|, A, R],
  )(
    pos: SourcePos,
  )(using
    lambdas.Context,
  ): Validated[UnusedInBranch, $[R]] = {
    type -?>[X, Y] = PartialFun[X, Y]

    given CocartesianSemigroupalCategory[-?>, |+|] with {
      override def andThen[A, B, C](f: A -?> B, g: B -?> C): A -?> C = f > g
      override def id[A]: A -?> A = FreeScaletto.id
      override def injectL[A, B]: A -?> (A |+| B) = FreeScaletto.this.injectL
      override def injectR[A, B]: B -?> (A |+| B) = FreeScaletto.this.injectR
      override def either[A, B, C](f: A -?> C, g: B -?> C): (A |+| B) -?> C =
        (total(f) zip total(g)) match
          case Valid((f, g)) => FreeScaletto.this.either(f, g)
          case Invalid(es)   => raiseTotalityViolations(es) // XXX
    }

    given Distribution[-?>, |*|, |+|] with {
      override val cat: SemigroupalCategory[-?>, |*|] = summon

      override def distLR[A, B, C]: (A |*| (B |+| C)) -?> ((A |*| B) |+| (A |*| C)) =
        FreeScaletto.this.distributeL

      override def distRL[A, B, C]: ((A |+| B) |*| C) -?> ((A |*| C) |+| (B |*| C)) =
        FreeScaletto.this.distributeR
    }

    CapturingFun.compileSink[PartialFun, |*|, |+|, lambdas.Expr, ScopeInfo, A, R](
      cases,
    )(
      [X] => x => lambdas.Context.exprDiscarders(x).map(_._1),
    ).map {
      case CapturingFun.NoCapture(f)  => lambdas.Expr.map(a, f)(VarOrigin.FunAppRes(pos))
      case CapturingFun.Closure(x, f) => mapTupled(Tupled.zip(x, Tupled.atom(a)), f)(pos)
    }.emap { case (c, exprs) =>
      PatternMatching.UnusedInBranch(Var.Set.fromList(exprs.toList.map(_.value.resultVar)), c)
    }
  }

  override def switch[A, R](using
    ctx: LambdaContext,
    switchPos: SourcePos,
  )(
    a: $[A],
  )(
    cases: (SourcePos, LambdaContext ?=> $[A] => $[R])*
  ): $[R] =
    cases.toList match
      case Nil =>
        throw IllegalArgumentException("switch must have at least 1 case")
      case c :: cs =>
        switchImpl(switchPos, a, NonEmptyList(c, cs))
          .getOrReportErrors

  private case class MisplacedExtractor(ext: ExtractorOccurrence[?, ?])

  private case class PatternMatchError(switchPos: SourcePos, error: patmat.PatternMatchError)

  private type SwitchRes[T] = Validated[LinearityViolation | UnusedInBranch | MisplacedExtractor | PatternMatchError, T]

  extension [T](r: SwitchRes[T]) {
    private def getOrReportErrors: T =
      r match
        case Valid(value) => value
        case Invalid(errors) => assemblyErrors(errors)
  }

  private def switchImpl[A, R](
    switchPos: SourcePos,
    scrutinee: $[A],
    cases: NonEmptyList[(SourcePos, LambdaContext ?=> $[A] => $[R])],
  )(using
    ctx: LambdaContext,
  ): SwitchRes[$[R]] = {
    import CapturingFun.{Closure, NoCapture}

    val inVar  = VarOrigin.SwitchIn(switchPos)
    val outVar = VarOrigin.SwitchOut(switchPos)
    val cases1: NonEmptyList[(ScopeInfo, VarOrigin, LambdaContext ?=> $[A] => $[R])] =
      cases.map { case (pos, f) => (ScopeInfo.SwitchCase(pos), VarOrigin.SwitchCase(pos), f) }

    patmat
      .forLambdas(lambdas)(
        isExtractor =
          [X, Y] => (f: PartialFun[X, Y]) =>
            f match {
              case eo: ExtractorOccurrence[X, Y] => Some(eo.ext)
              case _ => None
            },
        lower =
          [X, Y] => (f: PartialFun[X, Y]) =>
            f match {
              case f: (X -⚬ Y) => Valid(f)
              case f: ExtractorOccurrence[x, y] => invalid(MisplacedExtractor(f))
            },
        lift = [X, Y] => (f: X -⚬ Y) => (f: PartialFun[X, Y]),
      )
      .delambdifyAndCompile(scrutinee, inVar, outVar, cases1)
      .emap {
        case e: LinearityViolation => e
        case e: UnusedInBranch => e
        case e: MisplacedExtractor => e
        case e: patmat.PatternMatchError => PatternMatchError(switchPos, e)
      }
  }

  override val λ = new LambdaOps {
    override def apply[A, B](using pos: SourcePos)(f: lambdas.Context ?=> $[A] => $[B]): A -⚬ B =
      compile(f)(pos)

    private def recLocal[A, B](using pos: SourcePos, ctx: LambdaContext)(
      f: LambdaContext ?=> $[Sub[A, B]] => $[A] => $[B],
    ): MetaFun[A, B] =
      given Comonoid[Sub[A, B]] =
        comonoidSub[A, B]

      val f1: LambdaContext ?=> $[Sub[A, B] |*| A] => $[B] =
        { case *(self) |*| a => f(self)(a) }

      val g: MetaFun[Sub[A, B] |*| A, B] =
        compileMeta(f1)(pos)

      import CapturingFun.{Closure, NoCapture}

      g match
        case NoCapture(g) =>
          NoCapture(FreeScaletto.rec(g))
        case Closure(x, g) =>
          recLocalWithCapture(pos, x, g)

    private def recLocalWithCapture[X, A, B](
      recFunPos: SourcePos,
      x: Tupled[|*|, $, X],
      f: (X |*| (Sub[A, B] |*| A)) -⚬ B
    )(using
      LambdaContext
    ): MetaFun[A, B] =
      val dupX: X -⚬ (X |*| X) =
        multiDup(x)
          .valueOr { vs => assemblyError(MissingDupForRecFun(recFunPos, vs)) }
      val elimX: X -⚬ One =
        multiDiscard(x)
          .valueOr { vs => assemblyError(MissingDiscardForRecFun(recFunPos, vs)) }
      val g: (Sub[X |*| A, B] |*| (X |*| A)) -⚬ B =
        λ { case h |*| (x |*| a) =>
          val x1 |*| x2 = dupX(x)
          val h1: $[Sub[A, B]] =
            (h |*| x1) |> captureIntoSub(elimX, dupX)
          f(x2 |*| (h1 |*| a))
        }
      val h: (X |*| A) -⚬ B =
        FreeScaletto.rec(g)
      CapturingFun.Closure(x, h)

    private def multiDup[X](x: Tupled[|*|, $, X])(using lambdas.Context): Validated[Var[?], X -⚬ (X |*| X)] =
      import libretto.lambda.Bin.{Leaf, Branch}
      import Tupled.fromBin

      x.asBin match
        case Leaf(x) =>
          val v: Var[X] = x.resultVar
          lambdas.Context.getSplit(v) match
            case None => invalid(v)
            case Some(dup) =>
              dup match
                case ExtractorOccurrence(_, _) => throw AssertionError(s"TODO: make unrepresentable (at ${summon[SourcePos]})")
                case f: (X -⚬ (X |*| X))       => Valid(f: X -⚬ (X |*| X))
        case Branch(l, r) =>
          (multiDup(fromBin(l)) zip multiDup(fromBin(r)))
            .map { case (dup1, dup2) => andThen(par(dup1, dup2), 𝒞.ixi) }


    private def multiDiscard[X](x: Tupled[|*|, $, X])(using lambdas.Context): Validated[Var[?], X -⚬ One] =
      import libretto.lambda.Bin.{Leaf, Branch}
      import Tupled.fromBin

      x.asBin match
        case Leaf(x) =>
          val v: Var[X] = x.resultVar
          lambdas.Context.getDiscard(v) match
            case None => invalid(v)
            case Some((elimFst, _)) =>
              elimFst[One] match
                case ExtractorOccurrence(_, _) => throw AssertionError(s"TODO: make unrepresentable (at ${summon[SourcePos]})")
                case elimFst: ((X |*| One) -⚬ One) => Valid(andThen(introSnd[X], elimFst))
        case Branch(l, r) =>
          (multiDiscard(fromBin(l)) zip multiDiscard(fromBin(r)))
            .map { case (dis1, dis2) => andThen(par(dis1, dis2), elimFst) }

    override val closure: ClosureOps =
      new ClosureOps {
        override def apply[A, B](using pos: SourcePos, ctx: lambdas.Context)(
          f: lambdas.Context ?=> $[A] => $[B],
        ): $[A =⚬ B] =
          compileClosure(f)(pos)(using ctx)

        override def rec[A, B](using pos: SourcePos, ctx: LambdaContext)(
          f: LambdaContext ?=> $[Sub[A, B]] => $[A] => $[B],
        ): $[A =⚬ B] = {
          import CapturingFun.{Closure, NoCapture}

          val captVar   = VarOrigin.CapturedVars(pos)
          val resultVar = VarOrigin.ClosureVal(pos)

          recLocal(f) match
            case NoCapture(f) =>
              constant(obj(f))
            case Closure(captured, f) =>
              val x = lambdas.Expr.zipN(captured)(captVar)
              lambdas.Expr.map(x, 𝒞.curry(f))(resultVar)
        }
      }

    private def compile[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    ): A -⚬ B = {
      import CapturingFun.{Closure, NoCapture}

      val c = ScopeInfo.TopLevelLambda(pos)
      val a = VarOrigin.Lambda(pos)

      metaFunOrError(
        lambdas.delambdifyTopLevel(c, a, f)
      ) match {
        case NoCapture(f) =>
          f
        case Closure(captured, f) =>
          assemblyError(UnboundVariables(c, lambdas.Expr.initialVars(captured)))
      }
    }

    private def compileMeta[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    )(using
      ctx: lambdas.Context,
    ): MetaFun[A, B] = {
      val c = ScopeInfo.NestedLambda(pos)
      val a = VarOrigin.Lambda(pos)

      metaFunOrError(
        lambdas.delambdifyNested(c, a, f)
      )
    }

    private def compileClosure[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    )(using
      ctx: lambdas.Context,
    ): $[A =⚬ B] = {
      import CapturingFun.{Closure, NoCapture}

      val scopeInfo = ScopeInfo.NestedLambda(pos)
      val bindVar   = VarOrigin.Lambda(pos)
      val captVar   = VarOrigin.CapturedVars(pos)
      val resultVar = VarOrigin.ClosureVal(pos)

      metaFunOrError(
        lambdas.delambdifyNested[A, B](scopeInfo, bindVar, f)
      ) match {
        case Closure(captured, f) =>
          val x = lambdas.Expr.zipN(captured)(captVar)
          lambdas.Expr.map(x, 𝒞.curry(f))(resultVar)
        case NoCapture(f) =>
          val captured0 = $.one(using pos)
          (captured0 map 𝒞.curry(elimFst > f))(resultVar)
      }
    }

    private def metaFunOrError[A, B](
      res: Validated[LinearityViolation, lambdas.Delambdified[A, B]]
    ): MetaFun[A, B] =
      res match
        case Invalid(es) =>
          assemblyErrors(es)
        case Valid(f) =>
          f.traverseFun([x, y] => f => foldTotal(f)) match
            case Invalid(es) => raiseTotalityViolations(es)
            case Valid(f) => f
  }

  /** Preprocessed [[ValSwitch]]. */
  private sealed trait ValHandler[A, R] {
    def compile(using LambdaContext): Validated[
      LinearityViolation,
      Exists[[AA] =>> (Val[A] -⚬ AA, Sink[[x, y] =>> (ScopeInfo, lambdas.Delambdifold[x, y]), |+|, AA, R])]
    ]
  }

  private object ValDecomposition {
    class Last[A, R](
      pos: SourcePos,
      f: LambdaContext ?=> $[Val[A]] => $[R],
    ) extends ValHandler[A, R] {
      override def compile(using LambdaContext): Validated[
        LinearityViolation,
        Exists[[AA] =>> (Val[A] -⚬ AA, Sink[[x, y] =>> (ScopeInfo, lambdas.Delambdifold[x, y]), |+|, AA, R])]
      ] = {
        val scope = ScopeInfo.ValCase(pos)
        val label = VarOrigin.Lambda(pos)
        lambdas.delambdifyFoldNested(scope, label, f)
          .map { g => Exists((id[Val[A]], Sink((scope, g)))) }
      }
    }

    class Cons[A, H, T, R](
      partition: A => Either[H, T],
      pos: SourcePos,
      f: LambdaContext ?=> $[Val[H]] => $[R],
      t: ValHandler[T, R],
    ) extends ValHandler[A, R] {
      override def compile(using LambdaContext): Validated[
        LinearityViolation,
        Exists[[AA] =>> (Val[A] -⚬ AA, Sink[[x, y] =>> (ScopeInfo, lambdas.Delambdifold[x, y]), |+|, AA, R])]
      ] = {
        val scope = ScopeInfo.ValCase(pos)
        val h = lambdas.delambdifyFoldNested(scope, VarOrigin.Lambda(pos), f)
        (h zip t.compile).map { case (h, t) =>
          type AA = Val[H] |+| t.T
          val partition1: Val[A] -⚬ AA =
            mapVal(partition) > liftEither > either(injectL, t.value._1 > injectR)
          val sink: Sink[[x, y] =>> (ScopeInfo, lambdas.Delambdifold[x, y]), |+|, AA, R] =
            Sink.Join(Sink((scope, h)), t.value._2)
          Exists((partition1, sink))
        }
      }
    }

    def from[A, R](cases: ValSwitch.Cases[A, A, R]): ValHandler[A, R] =
      cases match {
        case c1: ValSwitch.FirstCase[a, a_, r] =>
          Last(c1.pos, c1.f)
        case cn: ValSwitch.NextCase[a, a1, a2, r] =>
          summon[a =:= A]
          // (a1 | a2) =:= A
          (from[a1, a2, R](
            (cn.base: ValSwitch.Cases[A, a1, R]).asInstanceOf[ValSwitch.Cases[a1 | a2, a1, R]],
            Last(cn.pos, cn.f),
          ): ValHandler[a1 | a2, R]).asInstanceOf[ValHandler[A, R]]
      }

    def from[A1, A2, R](
      cases: ValSwitch.Cases[A1 | A2, A1, R],
      acc: ValHandler[A2, R],
    ): ValHandler[A1 | A2, R] = {
      def prepend[X](pos: SourcePos, f: LambdaContext ?=> $[Val[X]] => $[R])(using TypeTest[X | A2, X]): ValHandler[X | A2, R] = {
        val partition: (X | A2) => Either[X, A2] = {
          case (x: X) => Left(x)
          case a2     => Right(a2.asInstanceOf[A2])
        }
        Cons[X | A2, X, A2, R](partition, pos, f, acc)
      }
      cases match {
        case c1: ValSwitch.FirstCase[a, a1, r] =>
          prepend[A1](c1.pos, c1.f)(using c1.typeTest)
        case cn: ValSwitch.NextCase[a, a10, a11, r] =>
          // a =:= (A1 | A2)
          // A1 =:= (a10 | a11)
          // Compiler does not infer these equations. See // https://github.com/lampepfl/dotty/issues/17075
          val ev = summon[A1 =:= A1].asInstanceOf[A1 =:= (a10 | a11)]
          (from[a10, a11 | A2, R](
            (cn.base: ValSwitch.Cases[a, a10, r]).asInstanceOf[ValSwitch.Cases[a10 | (a11 | A2), a10, R]],
            prepend[a11](cn.pos, cn.f)(using cn.typeTest),
          ): ValHandler[a10 | (a11 | A2), R])
            .asInstanceOf[ValHandler[A1 | A2, R]]
      }
    }
  }

  override def switchVal[A, R](
    a: $[Val[A]],
    cases: ValSwitch.Cases[A, A, R],
  )(pos: SourcePos)(using
    LambdaContext,
  ): $[R] =
    ValDecomposition.from(cases).compile
      .flatMap {
        case Exists.Some((partition, sink)) =>
          switchSink(
            $.map(a)(partition)(pos),
            sink,
          )(pos)
      }
      .valueOr(assemblyErrors)

  override val |*| : ConcurrentPairOps =
    new ConcurrentPairOps {}

  private def mapTupled[A, B](a: Tupled[|*|, lambdas.Expr, A], f: PartialFun[A, B])(pos: SourcePos)(using lambdas.Context): lambdas.Expr[B] =
    lambdas.Expr.map(
      lambdas.Expr.zipN(a)(VarOrigin.CapturedVars(pos)),
      f,
    )(VarOrigin.FunAppRes(pos))

  private type AssemblyErrorData =
    UnboundVariables
    | LinearityViolation
    | UnusedInBranch
    | MisplacedExtractor
    | PatternMatchError
    | MissingComonoidOpForRecFun
    | ForbiddenCaptureOfRecursiveCallsIntoLibCode

  private def assemblyError(e: AssemblyErrorData): Nothing =
    assemblyErrors(NonEmptyList.of(e))

  private def assemblyErrors(es: NonEmptyList[AssemblyErrorData]): Nothing =
    throw AssemblyError(es)

  override class AssemblyError private[FreeScaletto](
    errors: NonEmptyList[AssemblyErrorData]
  ) extends Exception(AssemblyError.formatMessages(errors))

  private object AssemblyError {

    def formatMessages(es: NonEmptyList[AssemblyErrorData]): String =
      val lines =
        es.toList.flatMap { e =>
          val NonEmptyList(line0, lines) = formatMessage(e)
          val l0 = s" * $line0"
          val ls = lines.map(l => s"   $l")
          l0 :: ls
        }
      ("Compilation errors:" :: lines).mkString("\n")

    /** Returns a list of lines. */
    def formatMessage(e: AssemblyErrorData): NonEmptyList[String] =
      e match
        case e: UnboundVariables   => unboundMsg(e)
        case e: LinearityViolation => linearityMsg(e)
        case e: UnusedInBranch     => unusedInBranchMsg(e)
        case e: MisplacedExtractor => misplacedExtMsg(e)
        case e: PatternMatchError  => patmatMsg(e)
        case e: MissingComonoidOpForRecFun => missingComonoidForRecFunMsg(e)
        case e: ForbiddenCaptureOfRecursiveCallsIntoLibCode => forbiddenCaptureOfRecursiveCallsIntoLibCodeMsg(e)

    private def unboundMsg(e: UnboundVariables): NonEmptyList[String] =
      val UnboundVariables(scope, vs) = e
      NonEmptyList(
        s"Undefined variables (possibly from outer context) when compiling ${scope.print}:",
        vs.list.map(v => s"- $v") :+ "Consider using λ.closure instead."
      )

    private def linearityMsg(e: LinearityViolation): NonEmptyList[String] = {
      import Lambdas.LinearityViolation.{Overused, Unused}

      def overusedMsg(vs: Var.Set[VarOrigin], exitedScope: ScopeInfo): NonEmptyList[String] =
        NonEmptyList(
          s"Variables used more than once when compiling ${exitedScope.print}:",
          vs.list.map(v => s" - ${v.origin.print}")
        )

      def unusedMsg[A](v: Var[A], exitedScope: ScopeInfo): NonEmptyList[String] =
        NonEmptyList.of(
          s"Unused variable: ${v.origin.print}",
          s"When exiting scope: ${exitedScope.print}",
        )

      e match
        case Overused(vs, ctxInfo) => overusedMsg(vs, ctxInfo)
        case Unused(v, ctxInfo)    => unusedMsg(v, ctxInfo)
    }

    def unusedInBranchMsg(e: UnusedInBranch): NonEmptyList[String] =
      val UnusedInBranch(vs, scope) = e
      val pos = scope.sourcePos
      NonEmptyList(
        s"Case at ${pos.filename}:${pos.line} has unused variables which are used by some of the other cases:",
        vs.list.map(v => s" - ${v.origin.print}")
      )

    private def misplacedExtMsg(e: MisplacedExtractor): NonEmptyList[String] =
      e match { case MisplacedExtractor(ExtractorOccurrence(ext, pos)) =>
        NonEmptyList.of(s"Extractor used outside of switch pattern: ${ext.show} (at ${pos.filename}:${pos.line})")
      }

    private def patmatMsg(e: PatternMatchError): NonEmptyList[String] =
      import patmat.PatternMatchError.{IncompatibleExtractors, NonExhaustiveness}

      val PatternMatchError(switchPos, error) = e

      error match
        case IncompatibleExtractors(base, incompatibles) =>
          "Use of incompatible extractors:" ::
            s"    ${base.partition} (from ${base.partitioning})" ::
            s"  is incompatible with" ::
            incompatibles.map { ext =>
              s"  - ${ext.partition} (from ${ext.partitioning})"
            }
        case NonExhaustiveness(ext) =>
          NonEmptyList.of(
            "Non-exhaustive pattern match. It would fail on",
            s"  ${ext.show} (at ${switchPos.filename}:${switchPos.line})"
          )

    private def missingComonoidForRecFunMsg(e: MissingComonoidOpForRecFun): NonEmptyList[String] =
      e match
        case MissingDupForRecFun(pos, vs) =>
          NonEmptyList(
            s"Recursive function definition at ${pos.filename}:${pos.line} captures the following variables which lack the ability to be duplicated:",
            vs.list.map { v =>  s"  - ${v.origin.print}" }
            ::: List(
              "Note: duplication is needed for potential recursive invocation.",
              "Consider using the `case *(a)` extractor for each of the varaibles to register a Comonoid instance."
            )
          )
        case MissingDiscardForRecFun(pos, vs) =>
          NonEmptyList(
            s"Recursive function definition at ${pos.filename}:${pos.line} captures the following variables which lack the ability to be discarded:",
            vs.list.map { v =>  s"  - ${v.origin.print}" }
            ::: List(
              "Note: discarding is needed when there's no more recursive invocation.",
              "Consider using the `case *(a)` extractor for each of the varaibles to register a Comonoid instance."
            )
          )

    private def forbiddenCaptureOfRecursiveCallsIntoLibCodeMsg(e: ForbiddenCaptureOfRecursiveCallsIntoLibCode): NonEmptyList[String] =
      val ForbiddenCaptureOfRecursiveCallsIntoLibCode(defnPos, refs) = e
      NonEmptyList(
        s"Library code defininition at ${defnPos.filename}:${defnPos.line} attempts to capture self-references to parent recursive functions:",
        refs.map { ref =>
          val p = ref.defnPos
          s" - Recursive function defined at ${p.filename}:${p.line}"
        }.toList
      ) :+ s"Consider rewriting the library function as taking a `Sub`-routine instead of capturing a self-reference."
  }

  private case class UnboundVariables(scope: ScopeInfo, vs: Var.Set[VarOrigin])

  private sealed trait MissingComonoidOpForRecFun

  private case class MissingDupForRecFun(recFunPos: SourcePos, vs: Var.Set[VarOrigin])
    extends MissingComonoidOpForRecFun

  private object MissingDupForRecFun {
    def apply(recFunPos: SourcePos, vs: NonEmptyList[Var[?]]): MissingDupForRecFun =
      MissingDupForRecFun(recFunPos, Var.Set.fromList(vs.toList))
  }

  private case class MissingDiscardForRecFun(recFunPos: SourcePos, vs: Var.Set[VarOrigin])
    extends MissingComonoidOpForRecFun

  private object MissingDiscardForRecFun {
    def apply(recFunPos: SourcePos, vs: NonEmptyList[Var[?]]): MissingDiscardForRecFun =
      MissingDiscardForRecFun(recFunPos, Var.Set.fromList(vs.toList))
  }

  private case class ForbiddenCaptureOfRecursiveCallsIntoLibCode(
    libCodeDefnPos: SourcePos,
    capturedRefs: NonEmptyList[-⚬.SelfRef[?, ?]],
  )

  private def raiseTotalityViolations(es: NonEmptyList[(SourcePos, NonEmptyList[String])]): Nothing =
    libretto.lambda.UnhandledCase.raise(s"raiseTotalityViolations($es)")
}
