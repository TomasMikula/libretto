package libretto.scaletto.impl

import libretto.scaletto.Scaletto
import libretto.lambda.{AForest, ClosedSymmetricMonoidalCategory, Focus, Lambdas, LambdasImpl, Partitioning, Shuffled, Sink, Tupled, Var}
import libretto.lambda.Lambdas.Delambdified
import libretto.lambda.Partitioning.Partition
import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Monad.monadEither
import libretto.util.{Async, StaticValue}
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
  final class NArySum[Cases] private()
  final type OneOf[Cases] = NArySum[Cases]
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

  sealed trait NAryInjector[Label, A, Cases]:
    import NAryInjector.*

    final type Type = A

    def nonVoidResult(using ev: Cases =:= Void): Nothing

  object NAryInjector {
    case class InHead[Label, A, Tail]() extends NAryInjector[Label, A, (Label of A) :: Tail]:
      override def nonVoidResult(using ev: (Label of A) :: Tail =:= Void): Nothing =
        throw new AssertionError(s"Impossible")

    case class InTail[Label, A, HLbl, H, Tail](i: NAryInjector[Label, A, Tail]) extends NAryInjector[Label, A, (HLbl of H) :: Tail]:
      override def nonVoidResult(using ev: (HLbl of H) :: Tail =:= Void): Nothing =
        throw new AssertionError(s"Impossible")
  }

  sealed trait NAryDistLR[A, Cases] {
    type Out
  }

  object NAryDistLR {
    case class Empty[A]() extends NAryDistLR[A, Void] { override type Out = Void }
    case class Cons[A, HLbl, H, Tail, ATail](
      tail: NAryDistLR[A, Tail] { type Out = ATail },
    ) extends NAryDistLR[A, (HLbl of H) :: Tail] {
      override type Out = (HLbl of (A |*| H)) :: ATail
    }

    def cons[A, HLbl, H, Tail](
      tail: NAryDistLR[A, Tail],
    ): NAryDistLR[A, (HLbl of H) :: Tail] { type Out = (HLbl of (A |*| H)) :: tail.Out } =
      Cons[A, HLbl, H, Tail, tail.Out](tail)
  }

  sealed trait NAryHandlerBuilder[Cases, RemainingCases, R]
  object NAryHandlerBuilder {
    case class Empty[Cases, R]() extends NAryHandlerBuilder[Cases, Cases, R]
    case class Snoc[Cases, HLbl, H, T, R](
      init: NAryHandlerBuilder[Cases, (HLbl of H) :: T, R],
      last: H -⚬ R,
    ) extends NAryHandlerBuilder[Cases, T, R]

    def addHandler[Cases, HLbl, H, T, R](
      b: NAryHandlerBuilder[Cases, (HLbl of H) :: T, R],
      h: H -⚬ R,
    ): NAryHandlerBuilder[Cases, T, R] =
      Snoc(b, h)
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
    case class Absurd[A]() extends (Void -⚬ A)
    case class NAryInject[Label, A, Cases](i: NAryInjector[Label, A, Cases]) extends (A -⚬ OneOf[Cases])
    case class NArySumPeel[Label, A, Cases]() extends (OneOf[(Label of A) :: Cases] -⚬ (A |+| OneOf[Cases]))
    case class NArySumUnpeel[Label, A, Cases]() extends ((A |+| OneOf[Cases]) -⚬ OneOf[(Label of A) :: Cases])
    case class NArySumVoid() extends (OneOf[Void] -⚬ Void)
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

  override object OneOf extends OneOfModule {
    override type Injector[Label, A, Cases] = NAryInjector[Label, A, Cases]
    override type IsCaseOf[Label, Cases] = NAryInjector[Label, ?, Cases]
    override type Handlers[Cases, R] = NAryHandlerBuilder[Cases, Void, R]
    override type DistLR[A, Cases] = NAryDistLR[A, Cases]

    override def inject[Label, A, Cases](using i: Injector[Label, A, Cases]): A -⚬ OneOf[Cases] =
      NAryInject(i)

    override def switch[Cases, R](handlers: Handlers[Cases, R]): OneOf[Cases] -⚬ R =
      import NAryHandlerBuilder.{Empty, Snoc}

      def go[RemainingCases](
        handlers: Handlers.Builder[Cases, RemainingCases, R],
        remaining: OneOf[RemainingCases] -⚬ R,
      ): OneOf[Cases] -⚬ R =
        handlers match
          case Empty() =>
            remaining
          case Snoc(handlers, last) =>
            go(
              handlers,
              andThen(peel, either(last, remaining))
            )

      go(handlers, andThen(void, absurd[R]))

    override def peel[Label, A, Cases]: OneOf[(Label of A) :: Cases] -⚬ (A |+| OneOf[Cases]) =
      NArySumPeel()

    override def unpeel[Label, A, Cases]: (A |+| OneOf[Cases]) -⚬ OneOf[(Label of A) :: Cases] =
      NArySumUnpeel()

    override def void: OneOf[Void] -⚬ Void =
      NArySumVoid()

    override def distLR[A, Cases](using ev: DistLR[A, Cases]): (A |*| OneOf[Cases]) -⚬ OneOf[ev.Out] =
      distLR_[A, Cases, ev.Out]

    private def distLR_[A, Cases, ACases](using ev: DistLR[A, Cases] { type Out = ACases }): (A |*| OneOf[Cases]) -⚬ OneOf[ACases] =
      ev match
        case NAryDistLR.Empty() =>
          summon[Cases =:= Void]
          andThen(
            snd(andThen(void, absurd[-[A] |*| OneOf[ev.Out]])),
            andThen(assocRL, andThen(fst(backvert), elimFst))
          )
        case c: NAryDistLR.Cons[a, n, h, t, at] =>
          val ev1: (((n of (a |*| h)) :: at) =:= ACases) =
            summon[((n of (a |*| h)) :: at) =:= c.Out] andThen summon[c.Out =:= ACases]
          distLRIntoTail[A, n, h, t, at](c.tail).to(using ev1.liftCo[OneOf])

    private def distLRIntoTail[A, HLbl, H, Tail, ATail](
      ev: NAryDistLR[A, Tail] { type Out = ATail },
    ): (A |*| OneOf[(HLbl of H) :: Tail]) -⚬ OneOf[(HLbl of (A |*| H)) :: ATail] =
      λ { case a |*| cs =>
        peel(cs) switch {
          case Left(h)  => inject(using headInjector[HLbl, A |*| H, ATail])(a |*| h)
          case Right(t) => (a |*| t) :>> distLR(using ev) :>> injectR :>> unpeel
        }
      }

    override object Injector extends InjectorModule {
      override def apply[Label, Cases](c: IsCaseOf[Label, Cases]): Injector[Label, c.Type, Cases] =
        c
    }


    override def headInjector[HLbl, H, Tail]: Injector[HLbl, H, (HLbl of H) :: Tail] =
      NAryInjector.InHead()

    override def tailInjector[Lbl, A, HLbl, H, Tail](using j: Injector[Lbl, A, Tail]): Injector[Lbl, A, (HLbl of H) :: Tail] =
      NAryInjector.InTail(j)

    override def isCaseOf[Label, A, Cases](using i: Injector[Label, A, Cases]): IsCaseOf[Label, Cases] { type Type = A } =
      i

    override def distLRCons[A, Label, H, Tail](using
      tail: DistLR[A, Tail]
    ): DistLR[A, (Label of H) :: Tail] { type Out = (Label of (A |*| H)) :: tail.Out } =
      NAryDistLR.cons[A, Label, H, Tail](tail)

    override def distLRVoid[A]: DistLR[A, Void] { type Out = Void } =
      NAryDistLR.Empty[A]()

    override object Handlers extends HandlersModule {
      override type Builder[Cases, RemainingCases, R] =
        NAryHandlerBuilder[Cases, RemainingCases, R]

      override def apply[Cases, R]: Builder[Cases, Cases, R] =
        NAryHandlerBuilder.Empty()

      extension [Cases, R](b: Builder[Cases, Void, R])
        override def end: Handlers[Cases, R] =
          b

      extension [Cases, HLbl, H, T, R](b: Builder[Cases, (HLbl of H) :: T, R])
        override def caseOf[Lbl](using StaticValue[Lbl], Lbl =:= HLbl)(h: H -⚬ R): Builder[Cases, T, R] =
          NAryHandlerBuilder.addHandler(b, h)
    }
  }

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

  private type Extractor[A, B] =
    Partition[-⚬, |+|, A, B]

  private object Extractor {
    def apply[T, P](
      partitioning: Partitioning[-⚬, |+|, T],
      partition:    partitioning.Partition[P],
    ): Extractor[T, P] =
      new Partition(partitioning, partition)
  }

  private type PartialFun[A, B] =
    (A -⚬ B) | Extractor[A, B]

  private val psh: Shuffled[PartialFun, |*|] =
    Shuffled[PartialFun, |*|]

  private type -?>[A, B] = psh.Shuffled[A, B]

  private type Pattern[A, B] = AForest[Extractor, |*|, A, B]

  private type LinearityViolation = Lambdas.Error.LinearityViolation[VarOrigin]

  private def partial[A, B](f: A -⚬ B): (A -?> B) =
    psh.lift(f)

  private def total[A, B](f: A -?> B): TotalRes[A -⚬ B] =
    import TotalRes.given

    f.foldMapA(
      [X, Y] => (g: PartialFun[X, Y]) => {
        g match
          case g: (X -⚬ Y) =>
            TotalRes.success(g)
          case p: Partition[-⚬, |+|, X, Y] =>
            p.isTotal match
              case Some(g) => TotalRes.success(g)
              case None => libretto.lambda.UnhandledCase.raise(s"Non-exhaustive matcher $p")
      }
    )

  /** The result of extracting a total function from a partial one. */
  private type TotalRes[T] = Either[NonEmptyList[(SourcePos, NonEmptyList[String])], T]
  private object TotalRes {
    def success[T](value: T): TotalRes[T] =
      Right(value)

    def zip[A, B](a: TotalRes[A], b: TotalRes[B]): TotalRes[(A, B)] =
      (a, b) match
        case (Right(a), Right(b)) => Right((a, b))
        case (Right(a), Left(es)) => Left(es)
        case (Left(es), Right(a)) => Left(es)
        case (Left(es), Left(fs)) => Left(es ++ fs)

    given Applicative[TotalRes] with {
      override def ap[A, B](ff: TotalRes[A => B])(fa: TotalRes[A]): TotalRes[B] =
        TotalRes.zip(ff, fa).map { case (f, a) => f(a) }

      override def pure[A](a: A): TotalRes[A] =
        Right(a)
    }
  }

  private val lambdas: Lambdas[-?>, |*|, VarOrigin] =
    Lambdas[-?>, |*|, VarOrigin]()

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
      switchSink(
        ab,
        Sink[lambdas.VFun, |+|, A, C]((a, f1)) <+> Sink((b, f2)),
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
      val v = a.resultVar
      lambdas.Context.registerNonLinearOps(v)(
        split.map(partial),
        discard.map(f => [B] => (_: Unit) => partial(elimFst[A, B](f))),
      )
      a
    }
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
        TotalRes.zip(total(fx), total(fy)) match
          case Right((fx, fy)) => partial(either(fx, fy))
          case Left(es)        => raiseTotalityViolations(es)
      },
      [X, Y, Z] => (_: Unit) => partial(distributeL[X, Y, Z]),
    ) match {
      case Delambdified.Exact(f)      => lambdas.Expr.map(a, f)(VarOrigin.FunAppRes(pos))
      case Delambdified.Closure(x, f) => mapTupled(Tupled.zip(x, Tupled.atom(a)), f)(pos)
      case Delambdified.Failure(e)    => raiseError(e)
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
          .getOrThrow

  private case class NonExhaustiveness(
    // pos: SourcePos,
    // unhandledPatterns: NonEmptyList[Pattern[?, ?]],
    extractor: Extractor[?, ?],
  )

  private enum SwitchRes[T] {
    case Success(value: T)
    case Failure(errors: NonEmptyList[LinearityViolation | NonExhaustiveness])

    def flatMap[U](f: T => SwitchRes[U]): SwitchRes[U] =
      this match
        case Success(value) => f(value)
        case Failure(es) => Failure(es)


    def getOrThrow: T =
      this match
        case Success(value) => value
        case Failure(errors) => libretto.lambda.UnhandledCase.raise(s"SwitchRes.getOrThrow(${errors.toList})")
  }

  private object SwitchRes {
    def nonExhaustiveness[T](ext: Extractor[?, ?]): SwitchRes[T] =
      failure(NonExhaustiveness(ext))

    def misplacedExtractor[T](ext: Extractor[?, ?]): SwitchRes[T] =
      libretto.lambda.UnhandledCase.raise(s"SwitchRes.misplacedExtractor($ext)")

    def failure[T](e: LinearityViolation | NonExhaustiveness): SwitchRes[T] =
      SwitchRes.Failure(NonEmptyList(e, Nil))

    given Applicative[SwitchRes] with {
      override def pure[A](a: A): SwitchRes[A] =
        Success(a)

      override def ap[A, B](ff: SwitchRes[A => B])(fa: SwitchRes[A]): SwitchRes[B] =
        (ff, fa) match
          case (Success(f), Success(a)) => Success(f(a))
          case (Success(_), Failure(f)) => Failure(f)
          case (Failure(e), Success(_)) => Failure(e)
          case (Failure(e), Failure(f)) => Failure(e ++ f)
    }
  }

  private def switchImpl[A, R](using
    ctx: LambdaContext,
    switchPos: SourcePos,
  )(
    a: $[A],
    cases: NonEmptyList[(SourcePos, LambdaContext ?=> $[A] => $[R])],
  ): SwitchRes[$[R]] = {
    import SwitchRes.{Success, failure}

    for {
      // delambdify each case
      delams: NonEmptyList[Delambdified.Success[$, |*|, -?>, VarOrigin, A, R]] <-
        cases.traverse { case (pos, f) =>
          lambdas.delambdifyNested(VarOrigin.SwitchCase(pos), f) match
            case f: Delambdified.Success[expr, p, arr, v, a, r] => Success(f)
            case Delambdified.Failure(e) => failure(e)
        }

      // make each case capture the least common superset of captured expressions
      delamN: Delambdified[$, |*|, [a, b] =>> NonEmptyList[a -?> b], VarOrigin, A, R] =
        lambdas.leastCommonCapture(delams)

      res <- switchDelambdified(a, delamN)
    } yield res
  }

  private def switchDelambdified[A, R](using
    ctx: LambdaContext,
    switchPos: SourcePos,
  )(
    a: $[A],
    cases: Delambdified[$, |*|, [a, b] =>> NonEmptyList[a -?> b], VarOrigin, A, R],
  ): SwitchRes[$[R]] = {
    import libretto.lambda.Lambdas.Delambdified.{Exact, Closure, Failure}

    // split each case into a (pattern, handler) pair
    // and compile the resulting list of pairs
    // (after extending the pattern to cover any captured expressions)

    cases match
      case Exact(fs) =>
        for {
          cases <- fs.traverse(extractPatternAt(Focus.id, _))
          f     <- compilePatternMatch(cases)
        } yield
          (a map partial(f))(VarOrigin.SwitchOut(switchPos))

      case cl: Closure[exp, prod, arr, v, x, a, r] =>
        val xa: $[x |*| A] =
          lambdas.Expr.zipN(cl.captured zip Tupled.atom(a))(VarOrigin.SwitchIn(switchPos))
        for {
          cases <- cl.f.traverse(extractPatternAt(Focus.snd, _))

          // extend the patterns to the captured expressions
          cases1: NonEmptyList[Exists[[XY] =>> (Pattern[x |*| A, XY], XY -⚬ R)]] =
            cases.map { case Exists.Some((p, h)) => Exists((p.inSnd[x], h)) }

          f <- compilePatternMatch(cases1)
        } yield
          lambdas.Expr.map(xa, partial(f))(VarOrigin.SwitchOut(switchPos))

      case Failure(e) =>
        SwitchRes.failure(e)
  }

  private def compilePatternMatch[A, R](
    cases: NonEmptyList[Exists[[Y] =>> (Pattern[A, Y], Y -⚬ R)]],
  ): SwitchRes[A -⚬ R] =
    withFirstScrutineeOf(cases.head.value._1)(
      { case TypeEq(Refl()) =>
        // the first case catches all, remaining cases ignored
        SwitchRes.Success(cases.head.value._2.from[A])
      },
      [F[_], T] => (
        pos: Focus[|*|, F],
        scr: Partitioning[-⚬, |+|, T],
        ev:  A =:= F[T],
      ) =>
        ev match { case TypeEq(Refl()) =>
          scr.compileAt(
            pos,
            [X] => (p: scr.Partition[X]) => {
              val ext: Extractor[T, X] =
                Partitioning.Partition(scr, p)
              val matchingCases =
                collectCompatibleCases[F, T, X, R](cases.toList, pos, ext)
              matchingCases match
                case Nil =>
                  SwitchRes.nonExhaustiveness(Extractor(scr, p)) // TODO: include context of this extractor
                case c :: cs =>
                  compilePatternMatch[F[X], R](NonEmptyList(c, cs))
            }
          ).map(_.from[A])
        }
    )

  private def withFirstScrutineeOf[A, B, R](p: Pattern[A, B])(
    caseCatchAll: (A =:= B) => R,
    caseProper: [F[_], T] => (Focus[|*|, F], Partitioning[-⚬, |+|, T], A =:= F[T]) => R,
  ): R =
    libretto.lambda.UnhandledCase.raise(s"withFirstScrutineeOf($p)")

  private def collectCompatibleCases[F[_], T, U, R](
    cases: List[Exists[[Y] =>> (Pattern[F[T], Y], Y -⚬ R)]],
    pos: Focus[|*|, F],
    ext: Extractor[T, U],
  ): List[Exists[[Y] =>> (Pattern[F[U], Y], Y -⚬ R)]] =
    libretto.lambda.UnhandledCase.raise(s"collectCompatibleCases($cases, $pos, $ext)")

  private def extractPatternAt[F[_], A0, B](
    pos: Focus[|*|, F],
    f: F[A0] -?> B,
  ): SwitchRes[Exists[[X] =>> (Pattern[A0, X], F[X] -⚬ B)]] =
    f.extrudeInitForestAtWhile[F, A0, Extractor](
      pos,
      [X, Y] => (f: PartialFun[X, Y]) =>
        f match {
          case ex: Extractor[X, Y] => Some(ex)
          case _ => None
        }
    ) match
      case Exists.Some((pattern, handler)) =>
        handler
          .foldMapA[SwitchRes, -⚬](
            [X, Y] => (f: PartialFun[X, Y]) =>
              f match {
                case f: (X -⚬ Y) => SwitchRes.Success(f)
                case f: Extractor[x, y] => SwitchRes.misplacedExtractor(f)
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

      val a = VarOrigin.Lambda(pos)

      lambdas.delambdifyTopLevel(a, f) match {
        case Exact(f) =>
          total(f) match
            case Right(f) => f
            case Left(es) => raiseTotalityViolations(es)
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
      import Delambdified.{Closure, Exact, Failure}

      val bindVar   = VarOrigin.Lambda(pos)
      val captVar   = VarOrigin.CapturedVars(pos)
      val resultVar = VarOrigin.ClosureVal(pos)

      lambdas.delambdifyNested[A, B](bindVar, f) match {
        case Closure(captured, f) =>
          total(f) match
            case Right(f) =>
              val x = lambdas.Expr.zipN(captured)(captVar)
              lambdas.Expr.map(x, partial(ℭ.curry(f)))(resultVar)
            case Left(es) =>
              raiseTotalityViolations(es)
        case Exact(f) =>
          total(f) match
            case Right(f) =>
              val captured0 = $.one(using pos)
              (captured0 map partial(ℭ.curry(elimFst > f)))(resultVar)
            case Left(es) =>
              raiseTotalityViolations(es)
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

  private def raiseError(e: Lambdas.Error[VarOrigin]): Nothing = {
    import Lambdas.Error.Undefined
    import Lambdas.Error.LinearityViolation.{OverUnder, Overused, Underused}

    def overusedMsg(vs: Var.Set[VarOrigin])  = s"Variables used more than once: ${vs.list.map(v => s" - ${v.origin.print}").mkString("\n", "\n", "\n")}"
    def underusedMsg(vs: Var.Set[VarOrigin]) = s"Variables not fully consumed: ${vs.list.map(v => s" - ${v.origin.print}").mkString("\n", "\n", "\n")}"

    e match {
      case Overused(vs)    => throw LinearityException(overusedMsg(vs))
      case Underused(vs)   => throw LinearityException(underusedMsg(vs))
      case OverUnder(o, u) => throw LinearityException(s"${overusedMsg(o)}\n${underusedMsg(u)}")
      case Undefined(vs)   => throw UnboundVariablesException(vs)
    }
  }

  private def raiseTotalityViolations(es: NonEmptyList[(SourcePos, NonEmptyList[String])]): Nothing =
    libretto.lambda.UnhandledCase.raise(s"raiseTotalityViolations($es)")

  abstract class MalformedException(msg: String) extends Exception(msg)

  override class LinearityException(msg: String) extends MalformedException(msg)
  override class UnboundVariablesException(vs: Var.Set[VarOrigin]) extends MalformedException(vs.list.mkString(", "))
  override class TotalityException(msg: String) extends MalformedException(msg)
}
