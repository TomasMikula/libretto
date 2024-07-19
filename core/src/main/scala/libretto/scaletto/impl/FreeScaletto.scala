package libretto.scaletto.impl

import libretto.scaletto.Scaletto
import libretto.lambda.{AForest, CapturingFun, ClosedSymmetricMonoidalCategory, CocartesianSemigroupalCategory, CoproductPartitioning, Distribution, EnumModule, Focus, Lambdas, LambdasImpl, Member, Partitioning, PatternMatching, SemigroupalCategory, Shuffled, Sink, Tupled, Var}
import libretto.lambda.Partitioning.SubFun
import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, SourcePos, StaticValue, TypeEq, TypeEqK, Validated}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}
import libretto.lambda.util.Monad.monadEither
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration
import scala.reflect.TypeTest
import libretto.lambda.SymmetricSemigroupalCategory

object FreeScaletto extends Scaletto {
  sealed trait -⚬[A, B] {

    lazy val size: Long =
      this match
        case -⚬.Id() => 1
        case -⚬.AndThen(f, g) => 1 + f.size + g.size
        case -⚬.Par(f1, f2) => 1 + f1.size + f2.size
        case -⚬.IntroFst() => 1
        case -⚬.IntroSnd() => 1
        case -⚬.ElimFst() => 1
        case -⚬.ElimSnd() => 1
        case -⚬.AssocLR() => 1
        case -⚬.AssocRL() => 1
        case -⚬.Swap() => 1
        case -⚬.InjectL() => 1
        case -⚬.InjectR() => 1
        case -⚬.EitherF(f, g) => 1 + f.size + g.size
        case -⚬.Absurd() => 1
        case -⚬.OneOfInject(i) => 1
        case -⚬.OneOfPeel() => 1
        case -⚬.OneOfUnpeel() => 1
        case -⚬.OneOfExtractSingle() => 1
        case -⚬.ChooseL() => 1
        case -⚬.ChooseR() => 1
        case -⚬.Choice(f, g) => 1 + f.size + g.size
        case -⚬.PingF() => 1
        case -⚬.PongF() => 1
        case -⚬.DelayIndefinitely() => 1
        case -⚬.RegressInfinitely() => 1
        case -⚬.Fork() => 1
        case -⚬.Join() => 1
        case -⚬.ForkNeed() => 1
        case -⚬.JoinNeed() => 1
        case -⚬.NotifyDoneL() => 1
        case -⚬.NotifyNeedL() => 1
        case -⚬.ForkPing() => 1
        case -⚬.ForkPong() => 1
        case -⚬.JoinPing() => 1
        case -⚬.JoinPong() => 1
        case -⚬.StrengthenPing() => 1
        case -⚬.StrengthenPong() => 1
        case -⚬.JoinRTermini() => 1
        case -⚬.JoinLTermini() => 1
        case -⚬.NotifyEither() => 1
        case -⚬.NotifyChoice() => 1
        case -⚬.InjectLOnPing() => 1
        case -⚬.ChooseLOnPong() => 1
        case -⚬.DistributeL() => 1
        case -⚬.CoDistributeL() => 1
        case -⚬.RInvertSignal() => 1
        case -⚬.LInvertSignal() => 1
        case -⚬.RInvertPingPong() => 1
        case -⚬.LInvertPongPing() => 1
        case -⚬.RInvertTerminus() => 1
        case -⚬.LInvertTerminus() => 1
        case -⚬.RecF(f) => 1 + f(-⚬.Id().asInstanceOf[A -⚬ B]).size // XXX
        case -⚬.RecFun(f) => 1 + f.size
        case -⚬.InvokeRecCall() => 1
        case -⚬.IgnoreRecCall() => 1
        case -⚬.DupRecCall() => 1
        case -⚬.Pack() => 1
        case -⚬.Unpack() => 1
        case -⚬.RacePair() => 1
        case -⚬.SelectPair() => 1
        case -⚬.Forevert() => 1
        case -⚬.Backvert() => 1
        case -⚬.DistributeInversion() => 1
        case -⚬.FactorOutInversion() => 1
        case -⚬.CrashWhenDone(msg) => 1
        case -⚬.Delay() => 1
        case -⚬.LiftEither() => 1
        case -⚬.LiftPair() => 1
        case -⚬.UnliftPair() => 1
        case -⚬.MapVal(f) => 1
        case -⚬.ConstVal(a) => 1
        case -⚬.ConstNeg(a) => 1
        case -⚬.Neglect() => 1
        case -⚬.NotifyVal() => 1
        case -⚬.NotifyNeg() => 1
        case -⚬.DebugPrint(msg) => 1
        case -⚬.Acquire(acquire, release) => 1
        case -⚬.TryAcquire(acquire, release) => 1
        case -⚬.Release() => 1
        case -⚬.ReleaseWith(f) => 1
        case -⚬.Effect(f) => 1
        case -⚬.EffectWr(f) => 1
        case -⚬.TryEffectAcquire(f, release) => 1
        case -⚬.TryTransformResource(f, release) => 1
        case -⚬.TrySplitResource(f, release1, release2) => 1

  }

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
  final class ||[A, B] private()
  final class ::[Label, T] private ()
  final class OneOf[Cases] private()
  final class Rec[F[_]] private()
  final class RecCall[A, B] private()
  final class Inverted[A] private()
  final type -[A] = Inverted[A]
  final class Val[A] private()
  final class Res[A] private()
  final type UInt31 = Val[Int]

  given BiInjective[|*|] with {
    override def unapply[A, B, X, Y](ev: (A |*| B) =:= (X |*| Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given BiInjective[|+|] with {
    override def unapply[A, B, X, Y](ev: (A |+| B) =:= (X |+| Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given BiInjective[||] with {
    override def unapply[A, B, X, Y](ev: (A || B) =:= (X || Y)): (A =:= X, B =:= Y) =
      ev match { case TypeEq(Refl()) => (summon, summon) }
  }

  given biInjectiveFlippedSeparator: BiInjective[[x, y] =>> y || x] =
    BiInjective[||].flip

  given BiInjective[::] with {
    override def unapply[A, B, X, Y](ev: (A :: B) =:= (X :: Y)): (A =:= X, B =:= Y) =
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
    case class OneOfInject[Label, A, Cases](i: Member[[x, y] =>> y || x, ::, Label, A, Cases]) extends (A -⚬ OneOf[Cases])
    case class OneOfPeel[Label, A, Cases]() extends (OneOf[Cases || (Label :: A)] -⚬ (A |+| OneOf[Cases]))
    case class OneOfUnpeel[Label, A, Cases]() extends ((A |+| OneOf[Cases]) -⚬ OneOf[Cases || (Label :: A)])
    case class OneOfExtractSingle[Lbl, A]() extends (OneOf[Lbl :: A] -⚬ A)
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
    case class RecFun[A, B](f: (RecCall[A, B] |*| A) -⚬ B) extends (A -⚬ B)
    case class CaptureIntoRecCall[X, A, B](
      discardCapture: X -⚬ One,
      splitCapture: X -⚬ (X |*| X),
    ) extends ((RecCall[X |*| A, B] |*| X) -⚬ RecCall[A, B])
    case class InvokeRecCall[A, B]() extends ((RecCall[A, B] |*| A) -⚬ B)
    case class IgnoreRecCall[A, B]() extends (RecCall[A, B] -⚬ One)
    case class DupRecCall[A, B]() extends (RecCall[A, B] -⚬ (RecCall[A, B] |*| RecCall[A, B]))
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
    (f, g) match
      case (Id(), g) => g
      case (f, Id()) => f
      case _         => AndThen(f, g)

  override def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D) =
    (f, g) match
      case (Id(), Id()) => Id()
      case _            => Par(f, g)

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

  override def rec[A, B](f: (RecCall[A, B] |*| A) -⚬ B): A -⚬ B =
    RecFun(f)

  override def recCall[A, B]: (RecCall[A, B] |*| A) -⚬ B =
    InvokeRecCall()

  override def comonoidRecCall[A, B]: Comonoid[RecCall[A, B]] =
    new Comonoid[RecCall[A, B]]:
      override def counit: RecCall[A, B] -⚬ One = IgnoreRecCall()
      override def split: RecCall[A, B] -⚬ (RecCall[A, B] |*| RecCall[A, B]) = DupRecCall()

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

  given 𝒞: ClosedSymmetricMonoidalCategory[-⚬, |*|, One, =⚬] with {
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
      override val cat: SemigroupalCategory[-⚬, |*|] =
        𝒞

      override def distLR[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
        FreeScaletto.this.distributeL

      override def distRL[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C)) =
        FreeScaletto.this.distributeR
    }

  override val OneOf: EnumModule.LeftAssociative[-⚬, |*|, OneOf, ||, ::] =
    EnumModule.fromBinarySums[-⚬, |*|, |+|, OneOf, [x, y] =>> y || x, ::](
      inj = [Label, A, Cases] => (i: Member[[x, y] =>> y || x, ::, Label, A, Cases]) => OneOfInject(i),
      peel = [Label, A, Cases] => DummyImplicit ?=> OneOfPeel(),
      unpeel = [Label, A, Cases] => DummyImplicit ?=> OneOfUnpeel(),
      extract = [Label, A] => DummyImplicit ?=> OneOfExtractSingle(),
    )(using
      𝒞,
      cocat,
      distribution,
    )

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

  override opaque type LocalFun[A, B] = CapturingFun[-⚬, |*|, Tupled[|*|, $, _], A, B]

  override val `$`: FunExprOps = new FunExprOps {
    override def one(using pos: SourcePos, ctx: lambdas.Context): $[One] =
      lambdas.Expr.const([x] => (_: Unit) => introFst[x])(VarOrigin.OneIntro(pos))

    override def map[A, B](a: $[A])(f: A -⚬ B)(pos: SourcePos)(using
      lambdas.Context,
    ): $[B] =
      (a map f)(VarOrigin.FunAppRes(pos))

    override def mapLocal[A, B](a: $[A])(f: LocalFun[A, B])(pos: SourcePos)(using
      lambdas.Context,
    ): $[B] =
      f match
        case CapturingFun.NoCapture(f) =>
          (a map f)(VarOrigin.FunAppRes(pos))
        case CapturingFun.Closure(x, f) =>
          val xa = lambdas.Expr.zipN(x zip Tupled.atom(a))(VarOrigin.CapturedVarsAndFunArg(pos))
          lambdas.Expr.map(xa, f)(VarOrigin.FunAppRes(pos))

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
        discard.map(f => [B] => (_: DummyImplicit) ?=> elimFst[A, B](f)),
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
      lambdas.Context.exprDiscarder,
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

  override val λ = new LambdaOpsWithClosures {
    override def apply[A, B](using pos: SourcePos)(f: lambdas.Context ?=> $[A] => $[B]): A -⚬ B =
      compile(f)(pos)

    override def local[A, B](using pos: SourcePos, ctx: lambdas.Context)(f: lambdas.Context ?=> $[A] => $[B]): LocalFun[A, B] =
      compileLocal(f)(pos)

    override def recLocal[A, B](using pos: SourcePos, ctx: LambdaContext)(
      f: LambdaContext ?=> $[RecCall[A, B]] => $[A] => $[B],
    ): LocalFun[A, B] =
      given Comonoid[RecCall[A, B]] =
        comonoidRecCall[A, B]

      val g: LocalFun[RecCall[A, B] |*| A, B] =
        local { case *(self) |*| a => f(self)(a) }

      import CapturingFun.{Closure, NoCapture}

      g match
        case NoCapture(g) =>
          NoCapture(RecFun(g))
        case Closure(x, g) =>
          recLocalWithCapture(pos, x, g)

    private def recLocalWithCapture[X, A, B](
      recFunPos: SourcePos,
      x: Tupled[|*|, $, X],
      f: (X |*| (RecCall[A, B] |*| A)) -⚬ B
    )(using
      LambdaContext
    ): LocalFun[A, B] =
      val dupX: X -⚬ (X |*| X) =
        multiDup(x)
          .valueOr { vs => assemblyError(MissingDupForRecFun(recFunPos, vs)) }
      val elimX: X -⚬ One =
        multiDiscard(x)
          .valueOr { vs => assemblyError(MissingDiscardForRecFun(recFunPos, vs)) }
      val g: (RecCall[X |*| A, B] |*| (X |*| A)) -⚬ B =
        λ { case h |*| (x |*| a) =>
          val x1 |*| x2 = dupX(x)
          val h1: $[RecCall[A, B]] =
            (h |*| x1) :>> CaptureIntoRecCall(elimX, dupX)
          f(x2 |*| (h1 |*| a))
        }
      val h: (X |*| A) -⚬ B =
        RecFun(g)
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
            case Some(elimFst) =>
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
      }

    private def compile[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    ): A -⚬ B = {
      import CapturingFun.{Closure, NoCapture}

      val c = ScopeInfo.TopLevelLambda(pos)
      val a = VarOrigin.Lambda(pos)

      lambdas.delambdifyTopLevel(c, a, f) match {
        case Valid(NoCapture(f)) =>
          foldTotal(f) match
            case Valid(f) => f
            case Invalid(es) => raiseTotalityViolations(es)
        case Valid(Closure(captured, f)) =>
          raiseUndefinedVars(lambdas.Expr.initialVars(captured))
        case Invalid(es) =>
          assemblyErrors(es)
      }
    }

    private def compileLocal[A, B](f: lambdas.Context ?=> $[A] => $[B])(
      pos: SourcePos,
    )(using
      ctx: lambdas.Context,
    ): LocalFun[A, B] = {
      val c = ScopeInfo.NestedLambda(pos)
      val a = VarOrigin.Lambda(pos)

      lambdas.delambdifyNested(c, a, f) match {
        case Valid(f) =>
          f.traverseFun([x, y] => f => foldTotal(f)) match
            case Valid(f) => f
            case Invalid(es) => raiseTotalityViolations(es)
        case Invalid(es) =>
          assemblyErrors(es)
      }
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

      lambdas.delambdifyNested[A, B](scopeInfo, bindVar, f) match {
        case Valid(Closure(captured, f)) =>
          foldTotal(f) match
            case Valid(f) =>
              val x = lambdas.Expr.zipN(captured)(captVar)
              lambdas.Expr.map(x, 𝒞.curry(f))(resultVar)
            case Invalid(es) =>
              raiseTotalityViolations(es)
        case Valid(NoCapture(f)) =>
          foldTotal(f) match
            case Valid(f) =>
              val captured0 = $.one(using pos)
              (captured0 map 𝒞.curry(elimFst > f))(resultVar)
            case Invalid(es) =>
              raiseTotalityViolations(es)
        case Invalid(es) =>
          assemblyErrors(es)
      }
    }
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

  override val |*| : ConcurrentPairInvertOps =
    new ConcurrentPairInvertOps {}

  private def mapTupled[A, B](a: Tupled[|*|, lambdas.Expr, A], f: PartialFun[A, B])(pos: SourcePos)(using lambdas.Context): lambdas.Expr[B] =
    lambdas.Expr.map(
      lambdas.Expr.zipN(a)(VarOrigin.CapturedVars(pos)),
      f,
    )(VarOrigin.FunAppRes(pos))

  private type AssemblyErrorData =
    UnboundVariables | LinearityViolation | UnusedInBranch | MisplacedExtractor | PatternMatchError | MissingComonoidOpForRecFun

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

    private def unboundMsg(e: UnboundVariables): NonEmptyList[String] =
      NonEmptyList(
        "Undefined variables (possibly from outer context):",
        e.vs.list.map(v => s"- $v")
      )

    private def linearityMsg(e: LinearityViolation): NonEmptyList[String] = {
      import Lambdas.LinearityViolation.{Overused, Unused}

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

      e match
        case Overused(vs)       => overusedMsg(vs)
        case Unused(v, ctxInfo) => unusedMsg(v, ctxInfo)
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
            vs.list.map { v =>  s"  - ${v.origin}" }
            ::: List(
              "Note: duplication is needed for potential recursive invocation.",
              "Consider using the `case *(a)` extractor for each of the varaibles to register a Comonoid instance."
            )
          )
        case MissingDiscardForRecFun(pos, vs) =>
          NonEmptyList(
            s"Recursive function definition at ${pos.filename}:${pos.line} captures the following variables which lack the ability to be discarded:",
            vs.list.map { v =>  s"  - ${v.origin}" }
            ::: List(
              "Note: discarding is needed when there's no more recursive invocation.",
              "Consider using the `case *(a)` extractor for each of the varaibles to register a Comonoid instance."
            )
          )
  }

  private def raiseUndefinedVars(vs: Var.Set[VarOrigin]): Nothing =
    assemblyError(UnboundVariables(vs))

  private case class UnboundVariables(vs: Var.Set[VarOrigin])

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

  private def raiseTotalityViolations(es: NonEmptyList[(SourcePos, NonEmptyList[String])]): Nothing =
    libretto.lambda.UnhandledCase.raise(s"raiseTotalityViolations($es)")
}
