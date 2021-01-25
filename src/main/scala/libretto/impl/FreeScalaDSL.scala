package libretto.impl

import libretto.{Async, ScalaDSL}
import scala.concurrent.duration.FiniteDuration

object FreeScalaDSL extends ScalaDSL {
  override sealed trait -⚬[A, B]

  // The following types are all "imaginary", never instantiated, but we declare them as classes,
  // so that the Scala typechecker can infer that
  //  1. they are injective (e.g. that if `(A |*| B) =:= (C |*| D)` then `A =:= C` and `B =:= D`;
  //  2. they are all distinct types (e.g. `One` can never be unified with `Done`).
  // Unfortunately, the Scala typechecker doesn't take advantage of this information anyway.
  override final class One private()
  override final class Done private()
  override final class Need private()
  override final class RTerminus private()
  override final class LTerminus private()
  override final class |*|[A, B] private()
  override final class |+|[A, B] private()
  override final class |&|[A, B] private()
  override final class Rec[F[_]] private()
  override final class Val[A] private()
  override final class Neg[A] private()
  override final class Res[A] private()

  object -⚬ {
    case class Id[A]() extends (A -⚬ A)
    case class AndThen[A, B, C](f: A -⚬ B, g: B -⚬ C) extends (A -⚬ C)
    case class Par[A, B, C, D](
      f: A -⚬ B,
      g: C -⚬ D,
    ) extends ((A |*| C) -⚬ (B |*| D))
    case class IntroFst[B]() extends (B -⚬ (One |*| B))
    case class IntroSnd[A]() extends (A -⚬ (A |*| One))
    case class ElimFst[B]() extends ((One |*| B) -⚬ B)
    case class ElimSnd[A]() extends ((A |*| One) -⚬ A)
    case class TimesAssocLR[A, B, C]() extends (((A |*| B) |*| C) -⚬ (A |*| (B |*| C)))
    case class TimesAssocRL[A, B, C]() extends ((A |*| (B |*| C)) -⚬ ((A |*| B) |*| C))
    case class Swap[A, B]() extends ((A |*| B) -⚬ (B |*| A))
    case class InjectL[A, B]() extends (A -⚬ (A |+| B))
    case class InjectR[A, B]() extends (B -⚬ (A |+| B))
    case class EitherF[A, B, C](f: A -⚬ C, g: B -⚬ C) extends ((A |+| B) -⚬ C)
    case class ChooseL[A, B]() extends ((A |&| B) -⚬ A)
    case class ChooseR[A, B]() extends ((A |&| B) -⚬ B)
    case class Choice[A, B, C](f: A -⚬ B, g: A -⚬ C) extends (A -⚬ (B |&| C))
    case class DoneF() extends (One -⚬ Done)
    case class NeedF() extends (Need -⚬ One)
    case class DelayIndefinitely() extends (Done -⚬ RTerminus)
    case class RegressInfinitely() extends (LTerminus -⚬ Need)
    case class Fork() extends (Done -⚬ (Done |*| Done))
    case class Join() extends ((Done |*| Done) -⚬ Done)
    case class ForkNeed() extends ((Need |*| Need) -⚬ Need)
    case class JoinNeed() extends (Need -⚬ (Need |*| Need))
    case class JoinRTermini() extends ((RTerminus |*| RTerminus) -⚬ RTerminus)
    case class JoinLTermini() extends (LTerminus -⚬ (LTerminus |*| LTerminus))
    case class SignalEither[A, B]() extends ((A |+| B) -⚬ (Done |*| (A |+| B)))
    case class SignalChoice[A, B]() extends ((Need |*| (A |&| B)) -⚬ (A |&| B))
    case class InjectLWhenDone[A, B]() extends ((Done |*| A) -⚬ ((Done |*| A) |+| B))
    case class InjectRWhenDone[A, B]() extends ((Done |*| B) -⚬ (A |+| (Done |*| B)))
    case class ChooseLWhenNeed[A, B]() extends (((Need |*| A) |&| B) -⚬ (Need |*| A))
    case class ChooseRWhenNeed[A, B]() extends ((A |&| (Need |*| B)) -⚬ (Need |*| B))
    case class DistributeLR[A, B, C]() extends ((A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)))
    case class CoDistributeL[A, B, C]() extends (((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)))
    case class RInvertSignal() extends ((Done |*| Need) -⚬ One)
    case class LInvertSignal() extends (One -⚬ (Need |*| Done))
    case class RInvertTerminus() extends ((RTerminus |*| LTerminus) -⚬ One)
    case class LInvertTerminus() extends (One -⚬ (LTerminus |*| RTerminus))
    case class RecF[A, B](f: (A -⚬ B) => (A -⚬ B)) extends (A -⚬ B) { self =>
      val recursed: A -⚬ B = f(self)
    }
    case class Pack[F[_]]() extends (F[Rec[F]] -⚬ Rec[F])
    case class Unpack[F[_]]() extends (Rec[F] -⚬ F[Rec[F]])
    case class RaceCompletion() extends ((Done |*| Done) -⚬ (Done |+| Done))
    case class SelectRequest() extends ((Need |&| Need) -⚬ (Need |*| Need))

    case class Crash[A, B](msg: String) extends ((Done |*| A) -⚬ (Done |*| B))
    case class Delay(d: FiniteDuration) extends (Done -⚬ Done)
    case class Promise[A]() extends (One -⚬ (Neg[A] |*| Val[A]))
    case class Fulfill[A]() extends ((Val[A] |*| Neg[A]) -⚬ One)
    case class LiftEither[A, B]() extends (Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]))
    case class UnliftEither[A, B]() extends ((Val[A] |+| Val[B]) -⚬ Val[Either[A, B]])
    case class LiftPair[A, B]() extends (Val[(A, B)] -⚬ (Val[A] |*| Val[B]))
    case class UnliftPair[A, B]() extends ((Val[A] |*| Val[B]) -⚬ Val[(A, B)])
    case class LiftNegPair[A, B]() extends (Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B]))
    case class UnliftNegPair[A, B]() extends ((Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)])
    case class MapVal[A, B](f: A => B) extends (Val[A] -⚬ Val[B])
    case class ContramapNeg[A, B](f: A => B) extends (Neg[B] -⚬ Neg[A])
    case class ConstVal[A](a: A) extends (Done -⚬ Val[A])
    case class ConstNeg[A](a: A) extends (Neg[A] -⚬ Need)
    case class Neglect[A]() extends (Val[A] -⚬ Done)
    case class Inflate[A]() extends (Need -⚬ Neg[A])

    case class MVal[A, B](init: A => B) extends (Val[A] -⚬ Res[B])
    case class TryAcquireAsync[A, R, B, E](
      acquire: A => Async[Either[E, (R, B)]],
      release: R => Async[Unit],
    ) extends (Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])))
    case class ReleaseAsync[R, A, B](f: (R, A) => Async[B]) extends ((Res[R] |*| Val[A]) -⚬ Val[B])
    case class EffectAsync[R, A, B](f: (R, A) => Async[B]) extends ((Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]))
    case class EffectWrAsync[R, A](f: (R, A) => Async[Unit]) extends ((Res[R] |*| Val[A]) -⚬ Res[R])
    case class TryTransformResourceAsync[R, A, S, B, E](
      f: (R, A) => Async[Either[E, (S, B)]],
      release: S => Async[Unit],
    ) extends ((Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])))
  }

  import -⚬._

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

  override def timesAssocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C)) =
    TimesAssocLR()

  override def timesAssocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C) =
    TimesAssocRL()

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

  override def done: One -⚬ Done =
    DoneF()

  override def need: Need -⚬ One =
    NeedF()

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

  override def joinRTermini: (RTerminus |*| RTerminus) -⚬ RTerminus =
    JoinRTermini()

  override def joinLTermini: LTerminus -⚬ (LTerminus |*| LTerminus) =
    JoinLTermini()

  override def signalEither[A, B]: (A |+| B) -⚬ (Done |*| (A |+| B)) =
    SignalEither()

  override def signalChoice[A, B]: (Need |*| (A |&| B)) -⚬ (A |&| B) =
    SignalChoice()

  override def injectLWhenDone[A, B]: (Done |*| A) -⚬ ((Done |*| A) |+| B) =
    InjectLWhenDone()

  override def injectRWhenDone[A, B]: (Done |*| B) -⚬ (A |+| (Done |*| B)) =
    InjectRWhenDone()

  override def chooseLWhenNeed[A, B]: ((Need |*| A) |&| B) -⚬ (Need |*| A) =
    ChooseLWhenNeed()

  override def chooseRWhenNeed[A, B]: (A |&| (Need |*| B)) -⚬ (Need |*| B) =
    ChooseRWhenNeed()

  override def distributeLR[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
    DistributeLR()

  override def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)) =
    CoDistributeL()

  override def rInvertSignal: (Done |*| Need) -⚬ One =
    RInvertSignal()

  override def lInvertSignal: One -⚬ (Need |*| Done) =
    LInvertSignal()

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

  override def raceCompletion: (Done |*| Done) -⚬ (Done |+| Done) =
    RaceCompletion()

  override def selectRequest: (Need |&| Need) -⚬ (Need |*| Need) =
    SelectRequest()

  override def crash[A, B](msg: String): (Done |*| A) -⚬ (Done |*| B) =
    Crash(msg)

  override def delay(d: FiniteDuration): Done -⚬ Done =
    Delay(d)

  override def promise[A]: One -⚬ (Neg[A] |*| Val[A]) =
    Promise()

  override def fulfill[A]: (Val[A] |*| Neg[A]) -⚬ One =
    Fulfill()

  override def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]) =
    LiftEither()

  override def unliftEither[A, B]: (Val[A] |+| Val[B]) -⚬ Val[Either[A, B]] =
    UnliftEither()

  override def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B]) =
    LiftPair()

  override def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)] =
    UnliftPair()

  override def liftNegPair[A, B]: Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B]) =
    LiftNegPair()

  override def unliftNegPair[A, B]: (Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)] =
    UnliftNegPair()

  override def mapVal[A, B](f: A => B): Val[A] -⚬ Val[B] =
    MapVal(f)

  override def contramapNeg[A, B](f: A => B): Neg[B] -⚬ Neg[A] =
    ContramapNeg(f)

  override def constVal[A](a: A): Done -⚬ Val[A] =
    ConstVal(a)

  override def constNeg[A](a: A): Neg[A] -⚬ Need =
    ConstNeg(a)

  override def neglect[A]: Val[A] -⚬ Done =
    Neglect()

  override def inflate[A]: Need -⚬ Neg[A] =
    Inflate()

  override def mVal[A, B](init: A => B): Val[A] -⚬ Res[B] =
    MVal(init)

  override def tryAcquireAsync[A, R, B, E](
    acquire: A => Async[Either[E, (R, B)]],
    release: R => Async[Unit],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])) =
    TryAcquireAsync(acquire, release)

  override def releaseAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ Val[B] =
    ReleaseAsync(f)

  override def effectAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    EffectAsync(f)

  override def effectWrAsync[R, A](f: (R, A) => Async[Unit]): (Res[R] |*| Val[A]) -⚬ Res[R] =
    EffectWrAsync(f)

  override def tryTransformResourceAsync[R, A, S, B, E](
    f: (R, A) => Async[Either[E, (S, B)]],
    release: S => Async[Unit],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    TryTransformResourceAsync(f, release)
}
