package libretto.scaletto.impl

import libretto.scaletto.Scaletto
import libretto.lambda.{ClosedSymmetricMonoidalCategory, Lambdas, LambdasImpl, Sink, Tupled, Var}
import libretto.lambda.Lambdas.Abstracted
import libretto.lambda.util.{BiInjective, Exists, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Monad.monadEither
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration
import scala.reflect.TypeTest

abstract class FreeScaletto {
  sealed trait -⚬[A, B]

  /** Type of nested arrows. */
  type ->[A, B]

  // The following types are all "imaginary", never instantiated, but we declare them as classes,
  // so that the Scala typechecker can infer that
  //  1. they are injective (e.g. that if `(A |*| B) =:= (C |*| D)` then `A =:= C` and `B =:= D`;
  //  2. they are all distinct types (e.g. `One` can never be unified with `Done`).
  // Unfortunately, the Scala typechecker doesn't take advantage of this information anyway.
  final class One private()
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

  object -⚬ {
    case class Id[A]() extends (A -⚬ A)
    case class AndThen[A, B, C](f: A -> B, g: B -> C) extends (A -⚬ C)
    case class Par[A1, A2, B1, B2](
      f1: A1 -> B1,
      f2: A2 -> B2,
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
    case class EitherF[A, B, C](f: A -> C, g: B -> C) extends ((A |+| B) -⚬ C)
    case class ChooseL[A, B]() extends ((A |&| B) -⚬ A)
    case class ChooseR[A, B]() extends ((A |&| B) -⚬ B)
    case class Choice[A, B, C](f: A -> B, g: A -> C) extends (A -⚬ (B |&| C))
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
}

object FreeScaletto extends FreeScaletto with Scaletto {
  import -⚬.*

  override type ->[A, B] = A -⚬ B

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

  type Var[A] = libretto.lambda.Var[VarOrigin, A]

  val lambdas: Lambdas[-⚬, |*|, VarOrigin] =
    new LambdasImpl[-⚬, |*|, VarOrigin]

  override type $[A] = lambdas.Expr[A]

  override type LambdaContext = lambdas.Context

  override val `$`: FunExprOps = new FunExprOps {
    override def one(using pos: SourcePos, ctx: lambdas.Context): $[One] =
      lambdas.Expr.const([x] => (_: Unit) => introFst[x])(VarOrigin.OneIntro(pos))

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
      lambdas.switch(
        Sink[lambdas.VFun, |+|, A, C]((a, f1)) <+> Sink((b, f2)),
        [X, Y] => (fx: X -⚬ C, fy: Y -⚬ C) => either(fx, fy),
        [X, Y, Z] => (_: Unit) => distributeL[X, Y, Z],
      ) match {
        case Abstracted.Exact(f)      => map(ab)(f)(pos)
        case Abstracted.Closure(x, f) => map(zipExprs(Tupled.zip(x, Tupled.atom(ab))))(f)(pos)
        case Abstracted.Failure(e)    => raiseError(e)
      }
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
      val v = a.resultVar
      lambdas.Context.registerNonLinearOps(v)(split, discard.map(f => [B] => (_: Unit) => elimFst[A, B](f)))
      a
    }
  }

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
      import Abstracted.{Closure, Exact, Failure}

      val a = VarOrigin.Lambda(pos)

      lambdas.absTopLevel(a, f) match {
        case Exact(f) =>
          f.fold
        case Closure(captured, f) =>
          val undefinedVars: Var.Set[VarOrigin] =
            lambdas.Expr.initialVars(captured)
          raiseError(Lambdas.Error.Undefined(undefinedVars))
        case Failure(e) =>
          raiseError(e)
      }
    }

    private def compileClosure[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    )(using
      ctx: lambdas.Context,
    ): $[A =⚬ B] = {
      import Abstracted.{Closure, Exact, Failure}

      val bindVar   = VarOrigin.Lambda(pos)
      val resultVar = VarOrigin.ClosureVal(pos)

      lambdas.absNested[A, B](bindVar, f) match {
        case Closure(captured, f) =>
          (zipExprs(captured) map ℭ.curry(f.fold))(resultVar)
        case Exact(f) =>
          val captured0 = $.one(using pos)
          (captured0 map ℭ.curry(elimFst > f.fold))(resultVar)
        case Failure(e) =>
          raiseError(e)
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
        val label = VarOrigin.Lambda(pos)
        Exists((id[Val[A]], Sink((label, f))))
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
          Sink[lambdas.VFun, |+|, Val[H], R]((VarOrigin.Lambda(pos), f)) <+> tail.value._2
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
    lambdas.Context,
  ): $[R] =
    ValDecomposition.from(cases).compile match {
      case Exists.Some((partition, sink)) =>
        lambdas.switch(
          sink,
          [X, Y] => (fx: X -⚬ R, fy: Y -⚬ R) => either(fx, fy),
          [X, Y, Z] => (_: Unit) => distributeL[X, Y, Z],
        ) match {
          case Abstracted.Exact(f)      => $.map(a)(partition > f)(pos)
          case Abstracted.Closure(x, f) => $.map(zipExprs(Tupled.zip(x, Tupled.atom(a))))(snd(partition) > f)(pos)
          case Abstracted.Failure(e)    => raiseError(e)
        }
    }

  override val |*| : ConcurrentPairInvertOps =
    new ConcurrentPairInvertOps {}

  // TODO: avoid the need to create auxiliary pairings
  private def zipExprs[A](es: Tupled[|*|, lambdas.Expr, A])(using lambdas.Context): lambdas.Expr[A] =
    es.fold([x, y] => (ex: lambdas.Expr[x], ey: lambdas.Expr[y]) => {
      val v = VarOrigin.Synthetic(s"auxiliary pairing of ($ex, $ey)")
      lambdas.Expr.zip(ex, ey)(v)
    })

  private def raiseError(e: Lambdas.Error[VarOrigin]): Nothing = {
    import Lambdas.Error.Undefined
    import Lambdas.Error.LinearityViolation.{OverUnder, Overused, Underused}

    def overusedMsg(vs: Var.Set[VarOrigin])  = s"Variables used more than once: ${vs.list.map(v => s" - ${v.origin.print}").mkString("\n", "\n", "\n")}"
    def underusedMsg(vs: Var.Set[VarOrigin]) = s"Variables not fully consumed: ${vs.list.map(v => s" - ${v.origin.print}").mkString("\n", "\n", "\n")}"

    e match {
      case Overused(vs)    => throw NotLinearException(overusedMsg(vs))
      case Underused(vs)   => throw NotLinearException(underusedMsg(vs))
      case OverUnder(o, u) => throw NotLinearException(s"${overusedMsg(o)}\n${underusedMsg(u)}")
      case Undefined(vs)   => throw UnboundVariablesException(vs)
    }
  }

  override class NotLinearException(msg: String) extends Exception(msg)
  override class UnboundVariablesException(vs: Var.Set[VarOrigin]) extends Exception
}
