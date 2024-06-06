package libretto.scaletto.impl

import libretto.scaletto.Scaletto
import libretto.lambda.{AForest, ClosedSymmetricMonoidalCategory, CocartesianSemigroupalCategory, Distribution, EnumModule, Focus, Lambdas, LambdasImpl, Partitioning, Shuffled, Sink, Tupled, Var}
import libretto.lambda.Lambdas.Delambdified
import libretto.lambda.Partitioning.SubFun
import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, SourcePos, StaticValue, TypeEq, Validated}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Validated.{Invalid, Valid}
import libretto.lambda.util.Monad.monadEither
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration
import scala.reflect.TypeTest
import libretto.lambda.util.TypeEqK

object FreeScaletto extends Scaletto {
  sealed trait -⚬[A, B]

  // The following types are all "imaginary", never instantiated, but we declare them as classes,
  // so that the Scala typechecker can infer that
  //  1. they are injective (e.g. that if `(A |*| B) =:= (C |*| D)` then `A =:= C` and `B =:= D`;
  //  2. they are all distinct types (e.g. `One` can never be unified with `Done`).
  // Unfortunately, the Scala typechecker doesn't take advantage of this information anyway.
  final class One private()
  final class Void private()
  final class Done private()
  final class Need private()
  final class Ping private()
  final class Pong private()
  final class RTerminus private()
  final class LTerminus private()
  final class ConcurrentPair[A, B] private()
  final type |*|[A, B] = ConcurrentPair[A, B]
  final class |+|[A, B] private()
  final class |&|[A, B] private()
  final class ::[A, B] private()
  final infix class of[Label, T] private ()
  final class OneOf[Cases] private()
  final class Rec[F[_]] private()
  final class Inverted[A] private()
  final type -[A] = Inverted[A]
  final class Val[A] private()
  final class Res[A] private()
  final type UInt31 = Val[Int]

  // biInjectivePair
  given BiInjective[|*|] with {
    override def unapply[A, B, X, Y](ev: (A |*| B) =:= (X |*| Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given BiInjective[::] with {
    override def unapply[A, B, X, Y](ev: (A :: B) =:= (X :: Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given BiInjective[of] with {
    override def unapply[A, B, X, Y](ev: (A of B) =:= (X of Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  object -⚬ {
    case class Id[A]() extends (A -⚬ A)
    case class AndThen[A, B, C](f: A -⚬ B, g: B -⚬ C) extends (A -⚬ C)
    case class Par[A1, A2, B1, B2](
      f1: A1 -⚬ B1,
      f2: A2 -⚬ B2,
    ) extends ((A1 |*| A2) -⚬ (B1 |*| B2))
    case class IntroFst[B]() extends (B -⚬ (One |*| B))
    case class IntroSnd[A]() extends (A -⚬ (A |*| One))
    case class ElimFst[B]() extends ((One |*| B) -⚬ B)
    case class ElimSnd[A]() extends ((A |*| One) -⚬ A)
    case class AssocLR[A, B, C]() extends (((A |*| B) |*| C) -⚬ (A |*| (B |*| C)))
    case class AssocRL[A, B, C]() extends ((A |*| (B |*| C)) -⚬ ((A |*| B) |*| C))
    case class Swap[A, B]() extends ((A |*| B) -⚬ (B |*| A))
    case class InjectL[A, B]() extends (A -⚬ (A |+| B))
    case class InjectR[A, B]() extends (B -⚬ (A |+| B))
    case class EitherF[A, B, C](f: A -⚬ C, g: B -⚬ C) extends ((A |+| B) -⚬ C)
    case class Absurd[A]() extends (Void -⚬ A)
    case class OneOfInject[Label, A, Cases](i: EnumModule.Injector[::, of, Label, A, Cases]) extends (A -⚬ OneOf[Cases])
    case class OneOfPeel[Label, A, Cases]() extends (OneOf[(Label of A) :: Cases] -⚬ (A |+| OneOf[Cases]))
    case class OneOfUnpeel[Label, A, Cases]() extends ((A |+| OneOf[Cases]) -⚬ OneOf[(Label of A) :: Cases])
    case class OneOfExtractSingle[Lbl, A]() extends (OneOf[Lbl of A] -⚬ A)
    case class ChooseL[A, B]() extends ((A |&| B) -⚬ A)
    case class ChooseR[A, B]() extends ((A |&| B) -⚬ B)
    case class Choice[A, B, C](f: A -⚬ B, g: A -⚬ C) extends (A -⚬ (B |&| C))
    case class PingF() extends (One -⚬ Ping)
    case class PongF() extends (Pong -⚬ One)
    case class DelayIndefinitely() extends (Done -⚬ RTerminus)
    case class RegressInfinitely() extends (LTerminus -⚬ Need)
    case class Fork() extends (Done -⚬ (Done |*| Done))
    case class Join() extends ((Done |*| Done) -⚬ Done)
    case class ForkNeed() extends ((Need |*| Need) -⚬ Need)
    case class JoinNeed() extends (Need -⚬ (Need |*| Need))
    case class NotifyDoneL() extends (Done -⚬ (Ping |*| Done))
    case class NotifyNeedL() extends ((Pong |*| Need) -⚬ Need)
    case class ForkPing() extends (Ping -⚬ (Ping |*| Ping))
    case class ForkPong() extends ((Pong |*| Pong) -⚬ Pong)
    case class JoinPing() extends ((Ping |*| Ping) -⚬ Ping)
    case class JoinPong() extends (Pong -⚬ (Pong |*| Pong))
    case class StrengthenPing() extends (Ping -⚬ Done)
    case class StrengthenPong() extends (Need -⚬ Pong)
    case class JoinRTermini() extends ((RTerminus |*| RTerminus) -⚬ RTerminus)
    case class JoinLTermini() extends (LTerminus -⚬ (LTerminus |*| LTerminus))
    case class NotifyEither[A, B]() extends ((A |+| B) -⚬ (Ping |*| (A |+| B)))
    case class NotifyChoice[A, B]() extends ((Pong |*| (A |&| B)) -⚬ (A |&| B))
    case class InjectLOnPing[A, B]() extends ((Ping |*| A) -⚬ (A |+| B))
    case class ChooseLOnPong[A, B]() extends ((A |&| B) -⚬ (Pong |*| A))
    case class DistributeL[A, B, C]() extends ((A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)))
    case class CoDistributeL[A, B, C]() extends (((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)))
    case class RInvertSignal() extends ((Done |*| Need) -⚬ One)
    case class LInvertSignal() extends (One -⚬ (Need |*| Done))
    case class RInvertPingPong() extends ((Ping |*| Pong) -⚬ One)
    case class LInvertPongPing() extends (One -⚬ (Pong |*| Ping))
    case class RInvertTerminus() extends ((RTerminus |*| LTerminus) -⚬ One)
    case class LInvertTerminus() extends (One -⚬ (LTerminus |*| RTerminus))
    case class RecF[A, B](f: (A -⚬ B) => (A -⚬ B)) extends (A -⚬ B) { self =>
      val recursed: A -⚬ B = f(self)
    }
    case class Pack[F[_]]() extends (F[Rec[F]] -⚬ Rec[F])
    case class Unpack[F[_]]() extends (Rec[F] -⚬ F[Rec[F]])
    case class RacePair() extends ((Ping |*| Ping) -⚬ (One |+| One))
    case class SelectPair() extends ((One |&| One) -⚬ (Pong |*| Pong))

    case class Forevert[A]() extends (One -⚬ (-[A] |*| A))
    case class Backvert[A]() extends ((A |*| -[A]) -⚬ One)
    case class DistributeInversion[A, B]() extends (-[A |*| B] -⚬ (-[A] |*| -[B]))
    case class FactorOutInversion[A, B]() extends ((-[A] |*| -[B]) -⚬ -[A |*| B])

    case class CrashWhenDone[A, B](msg: String) extends ((Done |*| A) -⚬ B)
    case class Delay() extends (Val[FiniteDuration] -⚬ Done)
    case class LiftEither[A, B]() extends (Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]))
    case class LiftPair[A, B]() extends (Val[(A, B)] -⚬ (Val[A] |*| Val[B]))
    case class UnliftPair[A, B]() extends ((Val[A] |*| Val[B]) -⚬ Val[(A, B)])
    case class MapVal[A, B](f: ScalaFunction[A, B]) extends (Val[A] -⚬ Val[B])
    case class ConstVal[A](a: A) extends (Done -⚬ Val[A])
    case class ConstNeg[A](a: A) extends (-[Val[A]] -⚬ Need)
    case class Neglect[A]() extends (Val[A] -⚬ Done)
    case class NotifyVal[A]() extends (Val[A] -⚬ (Ping |*| Val[A]))
    case class NotifyNeg[A]() extends ((Pong |*| -[Val[A]]) -⚬ -[Val[A]])
    case class DebugPrint(msg: String) extends (Ping -⚬ One)

    case class Acquire[A, R, B](
      acquire: ScalaFunction[A, (R, B)],
      release: Option[ScalaFunction[R, Unit]],
    ) extends (Val[A] -⚬ (Res[R] |*| Val[B]))
    case class TryAcquire[A, R, B, E](
      acquire: ScalaFunction[A, Either[E, (R, B)]],
      release: Option[ScalaFunction[R, Unit]],
    ) extends (Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])))
    case class Release[R]() extends (Res[R] -⚬ Done)
    case class ReleaseWith[R, A, B](f: ScalaFunction[(R, A), B]) extends ((Res[R] |*| Val[A]) -⚬ Val[B])
    case class Effect[R, A, B](f: ScalaFunction[(R, A), B]) extends ((Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]))
    case class EffectWr[R, A](f: ScalaFunction[(R, A), Unit]) extends ((Res[R] |*| Val[A]) -⚬ Res[R])
    case class TryEffectAcquire[R, A, S, B, E](
      f: ScalaFunction[(R, A), Either[E, (S, B)]],
      release: Option[ScalaFunction[S, Unit]],
    ) extends ((Res[R] |*| Val[A]) -⚬ (Res[R] |*| (Val[E] |+| (Res[S] |*| Val[B]))))
    case class TryTransformResource[R, A, S, B, E](
      f: ScalaFunction[(R, A), Either[E, (S, B)]],
      release: Option[ScalaFunction[S, Unit]],
    ) extends ((Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])))
    case class TrySplitResource[R, A, S, T, B, E](
      f: ScalaFunction[(R, A), Either[E, (S, T, B)]],
      release1: Option[ScalaFunction[S, Unit]],
      release2: Option[ScalaFunction[T, Unit]],
    ) extends ((Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])))
  }

  import -⚬.*

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
    Id()

  override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C =
    AndThen(f, g)

  override def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D) =
    Par(f, g)

  override def introFst[B]: B -⚬ (One |*| B) =
    IntroFst()

  override def introSnd[A]: A -⚬ (A |*| One) =
    IntroSnd()

  override def elimFst[B]: (One |*| B) -⚬ B =
    ElimFst()

  override def elimSnd[A]: (A |*| One) -⚬ A =
    ElimSnd()

  override def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C)) =
    AssocLR()

  override def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C) =
    AssocRL()

  override def swap[A, B]: (A |*| B) -⚬ (B |*| A) =
    Swap()

  override def injectL[A, B]: A -⚬ (A |+| B) =
    InjectL()

  override def injectR[A, B]: B -⚬ (A |+| B) =
    InjectR()

  override def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C =
    EitherF(f, g)

  override def absurd[A]: Void -⚬ A =
    Absurd()

  override def chooseL[A, B]: (A |&| B) -⚬ A =
    ChooseL()

  override def chooseR[A, B]: (A |&| B) -⚬ B =
    ChooseR()

  override def choice[A, B, C](f: A -⚬ B, g: A -⚬ C): A -⚬ (B |&| C) =
    Choice(f, g)

  override def ping: One -⚬ Ping =
    PingF()

  override def pong: Pong -⚬ One =
    PongF()

  override def delayIndefinitely: Done -⚬ RTerminus =
    DelayIndefinitely()

  override def regressInfinitely: LTerminus -⚬ Need =
    RegressInfinitely()

  override def fork: Done -⚬ (Done |*| Done) =
    Fork()

  override def join: (Done |*| Done) -⚬ Done =
    Join()

  override def forkNeed: (Need |*| Need) -⚬ Need =
    ForkNeed()

  override def joinNeed: Need -⚬ (Need |*| Need) =
    JoinNeed()

  override def notifyDoneL: Done -⚬ (Ping |*| Done) =
    NotifyDoneL()

  override def notifyNeedL: (Pong |*| Need) -⚬ Need =
    NotifyNeedL()

  override def forkPing: Ping -⚬ (Ping |*| Ping) =
    ForkPing()

  override def forkPong: (Pong |*| Pong) -⚬ Pong =
    ForkPong()

  override def joinPing: (Ping |*| Ping) -⚬ Ping =
    JoinPing()

  override def joinPong: Pong -⚬ (Pong |*| Pong) =
    JoinPong()

  override def strengthenPing: Ping -⚬ Done =
    StrengthenPing()

  override def strengthenPong: Need -⚬ Pong =
    StrengthenPong()

  override def joinRTermini: (RTerminus |*| RTerminus) -⚬ RTerminus =
    JoinRTermini()

  override def joinLTermini: LTerminus -⚬ (LTerminus |*| LTerminus) =
    JoinLTermini()

  override def notifyEither[A, B]: (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    NotifyEither()

  override def notifyChoice[A, B]: (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    NotifyChoice()

  override def injectLOnPing[A, B]: (Ping |*| A) -⚬ (A |+| B) =
    InjectLOnPing()

  override def chooseLOnPong[A, B]: (A |&| B) -⚬ (Pong |*| A) =
    ChooseLOnPong()

  override def distributeL[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
    DistributeL()

  override def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)) =
    CoDistributeL()

  override def rInvertSignal: (Done |*| Need) -⚬ One =
    RInvertSignal()

  override def lInvertSignal: One -⚬ (Need |*| Done) =
    LInvertSignal()

  override def rInvertPingPong: (Ping |*| Pong) -⚬ One =
    RInvertPingPong()

  override def lInvertPongPing: One -⚬ (Pong |*| Ping) =
    LInvertPongPing()

  override def rInvertTerminus: (RTerminus |*| LTerminus) -⚬ One =
    RInvertTerminus()

  override def lInvertTerminus: One -⚬ (LTerminus |*| RTerminus) =
    LInvertTerminus()

  override def rec[A, B](f: (A -⚬ B) => (A -⚬ B)): A -⚬ B =
    RecF(f)

  override def unpack[F[_]]: Rec[F] -⚬ F[Rec[F]] =
    Unpack()

  override def pack[F[_]]: F[Rec[F]] -⚬ Rec[F] =
    Pack()

  override def racePair: (Ping |*| Ping) -⚬ (One |+| One) =
    RacePair()

  override def selectPair: (One |&| One) -⚬ (Pong |*| Pong) =
    SelectPair()

  override def crashWhenDone[A, B](msg: String): (Done |*| A) -⚬ B =
    CrashWhenDone(msg)

  override def delay: Val[FiniteDuration] -⚬ Done =
    Delay()

  override def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]) =
    LiftEither()

  override def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B]) =
    LiftPair()

  override def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)] =
    UnliftPair()

  override def mapVal[A, B](f: ScalaFun[A, B]): Val[A] -⚬ Val[B] =
    MapVal(f)

  override def constVal[A](a: A): Done -⚬ Val[A] =
    ConstVal(a)

  override def constNeg[A](a: A): Neg[A] -⚬ Need =
    ConstNeg(a)

  override def neglect[A]: Val[A] -⚬ Done =
    Neglect()

  override def notifyVal[A]: Val[A] -⚬ (Ping |*| Val[A]) =
    NotifyVal()

  override def notifyNeg[A]: (Pong |*| Neg[A]) -⚬ Neg[A] =
    NotifyNeg()

  override def debugPrint(msg: String): Ping -⚬ One =
    DebugPrint(msg)

  override def acquire[A, R, B](
    acquire: ScalaFun[A, (R, B)],
    release: Option[ScalaFun[R, Unit]],
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    Acquire(acquire, release)

  override def tryAcquire[A, R, B, E](
    acquire: ScalaFun[A, Either[E, (R, B)]],
    release: Option[ScalaFun[R, Unit]],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])) =
    TryAcquire(acquire, release)

  override def release[R]: Res[R] -⚬ Done =
    Release()

  override def releaseWith[R, A, B](f: ScalaFunction[(R, A), B]): (Res[R] |*| Val[A]) -⚬ Val[B] =
    ReleaseWith(f)

  override def effect[R, A, B](f: ScalaFunction[(R, A), B]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    Effect(f)

  override def effectWr[R, A](f: ScalaFunction[(R, A), Unit]): (Res[R] |*| Val[A]) -⚬ Res[R] =
    EffectWr(f)

  override def tryEffectAcquire[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| (Val[E] |+| (Res[S] |*| Val[B]))) =
    TryEffectAcquire(f, release)

  override def tryTransformResource[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    TryTransformResource(f, release)

  override def trySplitResource[R, A, S, T, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, T, B)]],
    release1: Option[ScalaFunction[S, Unit]],
    release2: Option[ScalaFunction[T, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])) =
    TrySplitResource(f, release1, release2)

  override def forevert[A]: One -⚬ (-[A] |*| A) =
    Forevert()

  override def backvert[A]: (A |*| -[A]) -⚬ One =
    Backvert()

  override def distributeInversion[A, B]: -[A |*| B] -⚬ (-[A] |*| -[B]) =
    DistributeInversion()

  override def factorOutInversion[A, B]: (-[A] |*| -[B]) -⚬ -[A |*| B] =
    FactorOutInversion()

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

  given ℭ: ClosedSymmetricMonoidalCategory[-⚬, |*|, One, =⚬] with {
    override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C                              = FreeScaletto.this.andThen(f, g)
    override def id[A]: A -⚬ A                                                               = FreeScaletto.this.id[A]
    override def par[A1, A2, B1, B2](f1: A1 -⚬ B1, f2: A2 -⚬ B2): (A1 |*| A2) -⚬ (B1 |*| B2) = FreeScaletto.this.par(f1, f2)
    override def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C))                    = FreeScaletto.this.assocLR[A, B, C]
    override def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C)                    = FreeScaletto.this.assocRL[A, B, C]
    override def swap[A, B]: (A |*| B) -⚬ (B |*| A)                                          = FreeScaletto.this.swap[A, B]
    override def elimFst[A]: (One |*| A) -⚬ A                                                = FreeScaletto.this.elimFst[A]
    override def elimSnd[A]: (A |*| One) -⚬ A                                                = FreeScaletto.this.elimSnd[A]
    override def introFst[A]: A -⚬ (One |*| A)                                               = FreeScaletto.this.introFst[A]
    override def introSnd[A]: A -⚬ (A |*| One)                                               = FreeScaletto.this.introSnd[A]
    override def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C)                            = FreeScaletto.this.curry(f)
    override def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B                                           = FreeScaletto.this.eval[A, B]
  }

  val cocat: CocartesianSemigroupalCategory[-⚬, |+|] =
    new CocartesianSemigroupalCategory[-⚬, |+|] {
      override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C = FreeScaletto.this.andThen(f, g)
      override def id[A]: A -⚬ A                                  = FreeScaletto.this.id[A]

      override def injectL[A, B]: A -⚬ (A |+| B)                         = FreeScaletto.this.injectL[A, B]
      override def injectR[A, B]: B -⚬ (A |+| B)                         = FreeScaletto.this.injectR[A, B]
      override def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C = FreeScaletto.this.either(f, g)
    }

  val distribution: Distribution[-⚬, |*|, |+|] =
    new Distribution[-⚬, |*|, |+|] {
      override def distLR[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
        FreeScaletto.this.distributeL

      override def distRL[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C)) =
        FreeScaletto.this.distributeR
    }

  override val OneOf: EnumModule[-⚬, |*|, OneOf, ::, of] =
    EnumModule.fromBinarySums[-⚬, |*|, |+|, OneOf, ::, of](
      inj = [Label, A, Cases] => (i: EnumModule.Injector[::, of, Label, A, Cases]) => OneOfInject(i),
      peel = [Label, A, Cases] => DummyImplicit ?=> OneOfPeel(),
      unpeel = [Label, A, Cases] => DummyImplicit ?=> OneOfUnpeel(),
      extract = [Label, A] => DummyImplicit ?=> OneOfExtractSingle(),
    )(using
      ℭ,
      cocat,
      distribution,
    )

  type Var[A] = libretto.lambda.Var[VarOrigin, A]

  private type Extractor[A, B] =
    Partitioning.Extractor[-⚬, |*|, A, B]

  private object Extractor {
    def apply[T, P](
      partitioning: Partitioning[-⚬, |*|, T],
      partition:    partitioning.Partition[P],
    ): Extractor[T, P] =
      partitioning.extractor(partition)
  }

  private case class ExtractorOccurrence[A, B](
    ext: Extractor[A, B],
    pos: SourcePos,
  )

  private type PartialFun[A, B] =
    (A -⚬ B) | ExtractorOccurrence[A, B]

  private val psh: Shuffled[PartialFun, |*|] =
    Shuffled[PartialFun, |*|]

  private type -?>[A, B] = psh.Shuffled[A, B]

  private type Pattern[A, B] = AForest[Extractor, |*|, A, B]

  private type LinearityViolation = Lambdas.LinearityViolation[VarOrigin, ScopeInfo]

  private def partial[A, B](f: A -⚬ B): (A -?> B) =
    psh.lift(f)

  private def total[A, B](f: A -?> B): TotalRes[A -⚬ B] =
    f.foldMapA(
      [X, Y] => (g: PartialFun[X, Y]) => {
        g match
          case g: (X -⚬ Y) =>
            TotalRes.success(g)
          case p: ExtractorOccurrence[X, Y] =>
            p.ext.isTotal match
              case Some(g) => TotalRes.success(g)
              case None => libretto.lambda.UnhandledCase.raise(s"Non-exhaustive matcher $p")
      }
    )

  /** The result of extracting a total function from a partial one. */
  private type TotalRes[T] = Validated[(SourcePos, NonEmptyList[String]), T]
  private object TotalRes {
    def success[T](value: T): TotalRes[T] =
      Valid(value)
  }

  private val lambdas: Lambdas[-?>, |*|, VarOrigin, ScopeInfo] =
    Lambdas[-?>, |*|, VarOrigin, ScopeInfo]()

  override opaque type $[A] = lambdas.Expr[A]

  override opaque type LambdaContext = lambdas.Context

  override val `$`: FunExprOps = new FunExprOps {
    override def one(using pos: SourcePos, ctx: lambdas.Context): $[One] =
      lambdas.Expr.const([x] => (_: Unit) => partial(introFst[x]))(VarOrigin.OneIntro(pos))

    override def map[A, B](a: $[A])(f: A -⚬ B)(pos: SourcePos)(using
      lambdas.Context,
    ): $[B] =
      (a map partial(f))(VarOrigin.FunAppRes(pos))

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
      lambdas.Expr.map(a, psh.lift(ExtractorOccurrence(extractor, pos)))(VarOrigin.ExtractorRes(pos))

    override def switchEither[A, B, C](
      ab: $[A |+| B],
      f: lambdas.Context ?=> Either[$[A], $[B]] => $[C],
    )(pos: SourcePos)(using
      lambdas.Context,
    ): $[C] = {
      val f1: lambdas.Context ?=> $[A] => $[C] = ctx ?=> a => f(Left(a))
      val f2: lambdas.Context ?=> $[B] => $[C] = ctx ?=> b => f(Right(b))
      val a = VarOrigin.Lambda(pos)
      val b = VarOrigin.Lambda(pos)
      val sl = ScopeInfo.LeftCase(pos)
      val sr = ScopeInfo.RightCase(pos)
      switchSink(
        ab,
        Sink[lambdas.VFun, |+|, A, C]((sl, a, f1)) <+> Sink((sr, b, f2)),
      )(pos)
    }

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
        split.map(partial),
        discard.map(f => [B] => (_: Unit) => partial(elimFst[A, B](f))),
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

  extension [F[_]](x: $[Rec[F]]) {
    override def unpackedMatchAgainst[B](ext: Extractor[F[Rec[F]], B])(using pos: SourcePos, ctx: LambdaContext): $[B] =
      val ext1 =
        ext.contramap[UnpackOnlyFun, Rec[F]](
          UnpackOnlyFun.Unpack[F](),
        )
      $.matchAgainst(x, ext1)(pos)
  }

  private def switchSink[A, R](
    a: $[A],
    cases: Sink[lambdas.VFun, |+|, A, R],
  )(
    pos: SourcePos,
  )(using
    lambdas.Context,
  ): $[R] =
    lambdas.switch(
      cases,
      [X, Y] => (fx: X -?> R, fy: Y -?> R) => {
        (total(fx) zip total(fy)) match
          case Valid((fx, fy)) => partial(either(fx, fy))
          case Invalid(es)     => raiseTotalityViolations(es)
      },
      [X, Y, Z] => (_: Unit) => partial(distributeL[X, Y, Z]),
    ) match {
      case Delambdified.Exact(f)      => lambdas.Expr.map(a, f)(VarOrigin.FunAppRes(pos))
      case Delambdified.Closure(x, f) => mapTupled(Tupled.zip(x, Tupled.atom(a)), f)(pos)
      case Delambdified.Failure(es)   => assemblyErrors(es)
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
        switchImpl(using ctx, switchPos)(a, NonEmptyList(c, cs))
          .getOrReportErrors

  private case class MisplacedExtractor(ext: ExtractorOccurrence[?, ?])

  private enum PatternMatchError:
    case IncompatibleExtractors(base: Extractor[?, ?], incompatible: NonEmptyList[Extractor[?, ?]])
    case NonExhaustiveness(switchPos: SourcePos, ext: Extractor[?, ?]) // TODO: include context

  private type SwitchRes[T] = Validated[LinearityViolation | MisplacedExtractor | PatternMatchError, T]

  extension [T](r: SwitchRes[T]) {
    private def getOrReportErrors: T =
      r match
        case Valid(value) => value
        case Invalid(errors) => assemblyErrors(errors)
  }

  private object SwitchRes {
    def nonExhaustiveness[T](switchPos: SourcePos, ext: Extractor[?, ?]): SwitchRes[T] =
      failure(PatternMatchError.NonExhaustiveness(switchPos, ext))

    def misplacedExtractor[T](ext: ExtractorOccurrence[?, ?]): SwitchRes[T] =
      failure(MisplacedExtractor(ext))

    def incompatibleExtractors[T](base: Extractor[?, ?], incompatible: NonEmptyList[Extractor[?, ?]]): SwitchRes[T] =
      failure(PatternMatchError.IncompatibleExtractors(base, incompatible))

    def failure[T](e: LinearityViolation | MisplacedExtractor | PatternMatchError): SwitchRes[T] =
      Invalid(NonEmptyList(e, Nil))
  }

  private def switchImpl[A, R](using
    ctx: LambdaContext,
    switchPos: SourcePos,
  )(
    a: $[A],
    cases: NonEmptyList[(SourcePos, LambdaContext ?=> $[A] => $[R])],
  ): SwitchRes[$[R]] =
    for {
      // delambdify each case
      delams: NonEmptyList[Delambdified.Success[$, |*|, -?>, VarOrigin, ScopeInfo, A, R]] <-
        cases.traverse { case (pos, f) =>
          lambdas.delambdifyNested(ScopeInfo.SwitchCase(pos), VarOrigin.SwitchCase(pos), f) match
            case f: Delambdified.Success[expr, p, arr, v, c, a, r] => Valid(f)
            case Delambdified.Failure(es) => Invalid(es)
        }

      // make each case capture the least common superset of captured expressions
      delamN: Delambdified[$, |*|, [a, b] =>> NonEmptyList[a -?> b], VarOrigin, ScopeInfo, A, R] =
        lambdas.leastCommonCapture(delams)

      res <- switchDelambdified(a, delamN)
    } yield res

  private def switchDelambdified[A, R](using
    ctx: LambdaContext,
    switchPos: SourcePos,
  )(
    a: $[A],
    cases: Delambdified[$, |*|, [a, b] =>> NonEmptyList[a -?> b], VarOrigin, ScopeInfo, A, R],
  ): SwitchRes[$[R]] = {
    import libretto.lambda.Lambdas.Delambdified.{Exact, Closure, Failure}

    // split each case into a (pattern, handler) pair
    // and compile the resulting list of pairs
    // (after extending the pattern to cover any captured expressions)

    cases match
      case Exact(fs) =>
        for {
          cases <- fs.traverse(extractPatternAt(Focus.id, _))
          f     <- compilePatternMatch(switchPos, cases)
        } yield
          (a map partial(f))(VarOrigin.SwitchOut(switchPos))

      case cl: Closure[exp, prod, arr, v, c, x, a, r] =>
        val xa: $[x |*| A] =
          lambdas.Expr.zipN(cl.captured zip Tupled.atom(a))(VarOrigin.SwitchIn(switchPos))
        for {
          cases <- cl.f.traverse(extractPatternAt(Focus.snd, _))

          // extend the patterns to the captured expressions
          cases1: NonEmptyList[Exists[[XY] =>> (Pattern[x |*| A, XY], XY -⚬ R)]] =
            cases.map { case Exists.Some((p, h)) => Exists((p.inSnd[x], h)) }

          f <- compilePatternMatch(switchPos, cases1)
        } yield
          lambdas.Expr.map(xa, partial(f))(VarOrigin.SwitchOut(switchPos))

      case Failure(es) =>
        Invalid(es)
  }

  private def compilePatternMatch[A, R](
    switchPos: SourcePos,
    cases: NonEmptyList[Exists[[Y] =>> (Pattern[A, Y], Y -⚬ R)]],
  ): SwitchRes[A -⚬ R] =
    withFirstScrutineeOf(cases.head.value._1)(
      { case TypeEq(Refl()) =>
        // the first case catches all, remaining cases ignored
        Valid(cases.head.value._2.from[A])
      },
      [F[_], T] => (
        pos: Focus[|*|, F],
        scr: Partitioning[-⚬, |*|, T],
        ev:  A =:= F[T],
      ) =>
        ev match { case TypeEq(Refl()) =>
          scr.compileAt(
            pos,
            [X] => (p: scr.Partition[X]) => {
              val ext: Extractor[T, X] =
                Extractor(scr, p)
              collectMatchingCases[F, T, X, R](cases.toList, pos, ext) match
                case Valid(matchingCases) =>
                  matchingCases match
                    case Nil =>
                      SwitchRes.nonExhaustiveness(switchPos, ext) // TODO: include context of this extractor
                    case c :: cs =>
                      compilePatternMatch[F[X], R](switchPos, NonEmptyList(c, cs))
                case Invalid(incompatibleExtractors) =>
                  SwitchRes.incompatibleExtractors(ext, incompatibleExtractors)
            }
          ).map(_.from[A])
        }
    )

  private def withFirstScrutineeOf[A, B, R](p: Pattern[A, B])(
    caseCatchAll: (A =:= B) => R,
    caseProper: [F[_], T] => (Focus[|*|, F], Partitioning[-⚬, |*|, T], A =:= F[T]) => R,
  ): R =
    p match
      case AForest.Node(extr, _) =>
        caseProper[[x] =>> x, A](Focus.id, extr.partitioning, summon)
      case AForest.Empty() =>
        caseCatchAll(summon)
      case AForest.Par(p1, p2) =>
        withFirstScrutineeOfPar(p1, p2)(caseCatchAll, caseProper)

  private def withFirstScrutineeOfPar[A1, A2, B1, B2, R](
    p1: Pattern[A1, B1],
    p2: Pattern[A2, B2],
  )(
    caseCatchAll: ((A1 |*| A2) =:= (B1 |*| B2)) => R,
    caseProper: [F[_], T] => (Focus[|*|, F], Partitioning[-⚬, |*|, T], (A1 |*| A2) =:= F[T]) => R,
  ): R =
    withFirstScrutineeOf(p1)(
      caseProper = { [F1[_], T1] => (f1: Focus[|*|, F1], ex1: Partitioning[-⚬, |*|, T1], ev1: A1 =:= F1[T1]) =>
        type F[T] = F1[T] |*| A2
        caseProper[F, T1](f1.inFst[A2], ex1, ev1.liftCo[[t] =>> t |*| A2])
      },
      caseCatchAll = { case TypeEq(Refl()) =>
        withFirstScrutineeOf(p2)(
          caseProper = { [F2[_], T2] => (f2: Focus[|*|, F2], ex2: Partitioning[-⚬, |*|, T2], ev2: A2 =:= F2[T2]) =>
            type F[T] = A1 |*| F2[T]
            caseProper[F, T2](f2.inSnd[A1], ex2, ev2.liftCo[[t] =>> A1 |*| t])
          },
          caseCatchAll = { case TypeEq(Refl()) =>
            caseCatchAll(summon)
          },
        )
      },
    )

  private def collectMatchingCases[F[_], T, U, R](
    cases: List[Exists[[Y] =>> (Pattern[F[T], Y], Y -⚬ R)]],
    pos: Focus[|*|, F],
    ext: Extractor[T, U],
  ): Validated[
    Extractor[?, ?], // incompatible extractors at the given position
    List[Exists[[Y] =>> (Pattern[F[U], Y], Y -⚬ R)]],
  ] =
    Applicative.traverseList(cases) {
      case Exists.Some((pattern, handler)) =>
        positExtractor(ext, pos, pattern, handler)
    }.map(_.flatten)

  private def positExtractor[T, U, F[_], Y, R](
    ext: Extractor[T, U],
    pos: Focus[|*|, F],
    pattern: Pattern[F[T], Y],
    handler: Y -⚬ R,
  ): Validated[
    Extractor[?, ?], // incompatible extractor at the given position in the given pattern
    Option[Exists[[Y] =>> (Pattern[F[U], Y], Y -⚬ R)]],
  ] =
    pattern.focus(pos) match
      case r: AForest.Focused.At[arr, pr, f, t, y, g] =>
        summon[Y =:= g[y]]
        val subpattern: Pattern[T, y] = r.target
        subpattern match
          case AForest.Empty() =>
            summon[T =:= y]
            val pattern1: Pattern[F[U], g[U]] = r.context[U]
            val handler1: g[U] -⚬ R = ext.reinject.at(r.context.outFocus) > handler
            Validated.Valid(Some(Exists((pattern1, handler1))))
          case AForest.Node(ext1, subpattern1) =>
            (ext sameAs ext1) match
              case None =>
                // incompatible partitionings
                Validated.invalid(ext1)
              case Some(None) =>
                // non-matching partitions
                Validated.Valid(None)
              case Some(Some(TypeEq(Refl()))) =>
                val pattern1 = r.context.plug(subpattern1)
                Validated.Valid(Some(Exists((pattern1, handler))))
          case AForest.Par(sp1, sp2) =>
            libretto.lambda.UnhandledCase.raise(s"incompatible extractors: $ext vs ($sp1, $sp2)")
      case AForest.Focused.IntoNode(fo, fi, node) =>
        Validated.invalid(node.value)

  private def extractPatternAt[F[_], A0, B](
    pos: Focus[|*|, F],
    f: F[A0] -?> B,
  ): SwitchRes[Exists[[X] =>> (Pattern[A0, X], F[X] -⚬ B)]] =
    f.takeLeadingForestAtWhile[F, A0, Extractor](
      pos,
      [X, Y] => (f: PartialFun[X, Y]) =>
        f match {
          case eo: ExtractorOccurrence[X, Y] => Some(eo.ext)
          case _ => None
        }
    ) match
      case Exists.Some((pattern, handler)) =>
        handler
          .foldMapA[SwitchRes, -⚬](
            [X, Y] => (f: PartialFun[X, Y]) =>
              f match {
                case f: (X -⚬ Y) => Valid(f)
                case f: ExtractorOccurrence[x, y] => SwitchRes.misplacedExtractor(f)
              }
          )
          .map(h => Exists((pattern, h)))

  override val λ = new LambdaOpsWithClosures {
    override def apply[A, B](using pos: SourcePos)(f: lambdas.Context ?=> $[A] => $[B]): A -⚬ B =
      compile(f)(pos)

    override val closure: ClosureOps =
      new ClosureOps {
        override def apply[A, B](using pos: SourcePos, ctx: lambdas.Context)(
          f: lambdas.Context ?=> $[A] => $[B],
        ): $[A =⚬ B] =
          compileClosure(f)(pos)(using ctx)
      }

    private def compile[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    ): A -⚬ B = {
      import Delambdified.{Closure, Exact, Failure}

      val c = ScopeInfo.TopLevelLambda(pos)
      val a = VarOrigin.Lambda(pos)

      lambdas.delambdifyTopLevel(c, a, f) match {
        case Exact(f) =>
          total(f) match
            case Valid(f) => f
            case Invalid(es) => raiseTotalityViolations(es)
        case Closure(captured, f) =>
          raiseUndefinedVars(lambdas.Expr.initialVars(captured))
        case Failure(es) =>
          assemblyErrors(es)
      }
    }

    private def compileClosure[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    )(using
      ctx: lambdas.Context,
    ): $[A =⚬ B] = {
      import Delambdified.{Closure, Exact, Failure}

      val scopeInfo = ScopeInfo.NestedLambda(pos)
      val bindVar   = VarOrigin.Lambda(pos)
      val captVar   = VarOrigin.CapturedVars(pos)
      val resultVar = VarOrigin.ClosureVal(pos)

      lambdas.delambdifyNested[A, B](scopeInfo, bindVar, f) match {
        case Closure(captured, f) =>
          total(f) match
            case Valid(f) =>
              val x = lambdas.Expr.zipN(captured)(captVar)
              lambdas.Expr.map(x, partial(ℭ.curry(f)))(resultVar)
            case Invalid(es) =>
              raiseTotalityViolations(es)
        case Exact(f) =>
          total(f) match
            case Valid(f) =>
              val captured0 = $.one(using pos)
              (captured0 map partial(ℭ.curry(elimFst > f)))(resultVar)
            case Invalid(es) =>
              raiseTotalityViolations(es)
        case Failure(es) =>
          assemblyErrors(es)
      }
    }
  }

  /** Preprocessed [[ValSwitch]]. */
  private sealed trait ValHandler[A, R] {
    def compile: Exists[[AA] =>> (Val[A] -⚬ AA, Sink[lambdas.VFun, |+|, AA, R])]
  }

  private object ValDecomposition {
    class Last[A, R](
      pos: SourcePos,
      f: LambdaContext ?=> $[Val[A]] => $[R],
    ) extends ValHandler[A, R] {
      override def compile: Exists[[AA] =>> (Val[A] -⚬ AA, Sink[lambdas.VFun, |+|, AA, R])] = {
        val scope = ScopeInfo.ValCase(pos)
        val label = VarOrigin.Lambda(pos)
        Exists((id[Val[A]], Sink((scope, label, f))))
      }
    }

    class Cons[A, H, T, R](
      partition: A => Either[H, T],
      pos: SourcePos,
      f: LambdaContext ?=> $[Val[H]] => $[R],
      t: ValHandler[T, R],
    ) extends ValHandler[A, R] {
      override def compile: Exists[[AA] =>> (Val[A] -⚬ AA, Sink[lambdas.VFun, |+|, AA, R])] = {
        val tail = t.compile
        type AA = Val[H] |+| tail.T
        val partition1: Val[A] -⚬ AA =
          mapVal(partition) > liftEither > either(injectL, tail.value._1 > injectR)
        val sink: Sink[lambdas.VFun, |+|, AA, R] =
          Sink[lambdas.VFun, |+|, Val[H], R]((ScopeInfo.ValCase(pos), VarOrigin.Lambda(pos), f)) <+> tail.value._2
        Exists((partition1, sink))
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
    ValDecomposition.from(cases).compile match {
      case Exists.Some((partition, sink)) =>
        switchSink(
          $.map(a)(partition)(pos),
          sink,
        )(pos)
    }

  override val |*| : ConcurrentPairInvertOps =
    new ConcurrentPairInvertOps {}

  private def mapTupled[A, B](a: Tupled[|*|, lambdas.Expr, A], f: A -?> B)(pos: SourcePos)(using lambdas.Context): lambdas.Expr[B] =
    lambdas.Expr.map(
      lambdas.Expr.zipN(a)(VarOrigin.CapturedVars(pos)),
      f,
    )(VarOrigin.FunAppRes(pos))

  private def assemblyError(e: UnboundVariables | LinearityViolation | MisplacedExtractor | PatternMatchError): Nothing =
    assemblyErrors(NonEmptyList.of(e))

  private def assemblyErrors(es: NonEmptyList[UnboundVariables | LinearityViolation | MisplacedExtractor | PatternMatchError]): Nothing =
    throw AssemblyError(es)

  override class AssemblyError private[FreeScaletto](
    errors: NonEmptyList[UnboundVariables | LinearityViolation | MisplacedExtractor | PatternMatchError]
  ) extends Exception(AssemblyError.formatMessages(errors))

  private object AssemblyError {

    def formatMessages(es: NonEmptyList[UnboundVariables | LinearityViolation | MisplacedExtractor | PatternMatchError]): String =
      val lines =
        es.toList.flatMap { e =>
          val NonEmptyList(line0, lines) = formatMessage(e)
          val l0 = s" * $line0"
          val ls = lines.map(l => s"   $l")
          l0 :: ls
        }
      ("Compilation errors:" :: lines).mkString("\n")

    /** Returns a list of lines. */
    def formatMessage(e: UnboundVariables | LinearityViolation | MisplacedExtractor | PatternMatchError): NonEmptyList[String] =
      e match
        case e: UnboundVariables   => unboundMsg(e)
        case e: LinearityViolation => linearityMsg(e)
        case e: MisplacedExtractor => misplacedExtMsg(e)
        case e: PatternMatchError  => patmatMsg(e)

    private def unboundMsg(e: UnboundVariables): NonEmptyList[String] =
      NonEmptyList(
        "Undefined variables (possibly from outer context):",
        e.vs.list.map(v => s"- $v")
      )

    private def linearityMsg(e: LinearityViolation): NonEmptyList[String] = {
      import Lambdas.LinearityViolation.{Overused, Unused, UnusedInBranch}

      def overusedMsg(vs: Var.Set[VarOrigin]): NonEmptyList[String] =
        NonEmptyList(
          "Variables used more than once:",
          vs.list.map(v => s" - ${v.origin.print}")
        )

      def unusedMsg[A](v: Var[A], exitedScope: ScopeInfo): NonEmptyList[String] =
        NonEmptyList.of(
          s"Unused variable: ${v.origin.print}",
          s"When exiting scope: ${exitedScope.print}",
        )

      def unusedInBranchMsg(vs: Var.Set[VarOrigin]): NonEmptyList[String] =
        NonEmptyList(
          "Variables not used in all branches:",
          vs.list.map(v => s" - ${v.origin.print}")
        )

      e match
        case Overused(vs)       => overusedMsg(vs)
        case Unused(v, ctxInfo) => unusedMsg(v, ctxInfo)
        case UnusedInBranch(vs) => unusedInBranchMsg(vs)
    }

    private def misplacedExtMsg(e: MisplacedExtractor): NonEmptyList[String] =
      e match { case MisplacedExtractor(ExtractorOccurrence(ext, pos)) =>
        NonEmptyList.of(s"Extractor used outside of switch pattern: ${ext.show} (at ${pos.filename}:${pos.line})")
      }

    private def patmatMsg(e: PatternMatchError): NonEmptyList[String] =
      e match
        case PatternMatchError.IncompatibleExtractors(base, incompatibles) =>
          "Use of incompatible extractors:" ::
            s"    ${base.partition} (from ${base.partitioning})" ::
            s"  is incompatible with" ::
            incompatibles.map { ext =>
              s"  - ${ext.partition} (from ${ext.partitioning})"
            }
        case PatternMatchError.NonExhaustiveness(switchPos, ext) =>
          NonEmptyList.of(
            "Non-exhaustive pattern match. It would fail on",
            s"  ${ext.show} (at ${switchPos.filename}:${switchPos.line})"
          )
  }

  private def raiseUndefinedVars(vs: Var.Set[VarOrigin]): Nothing =
    assemblyError(UnboundVariables(vs))

  private case class UnboundVariables(vs: Var.Set[VarOrigin])

  private def raiseTotalityViolations(es: NonEmptyList[(SourcePos, NonEmptyList[String])]): Nothing =
    libretto.lambda.UnhandledCase.raise(s"raiseTotalityViolations($es)")
}
