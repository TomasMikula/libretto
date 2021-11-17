package libretto.impl

import libretto.{Async, BiInjective, ScalaDSL}
import libretto.scalasource
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
  override final class Ping private()
  override final class Pong private()
  override final class RTerminus private()
  override final class LTerminus private()
  override final class |*|[A, B] private()
  override final class |+|[A, B] private()
  override final class |&|[A, B] private()
  override final class Rec[F[_]] private()
  override final class -[A] private()
  override final class Val[A] private()
  override final class Res[A] private()

  implicit val biInjectivePair: BiInjective[|*|] =
    new BiInjective[|*|] {
      override def unapply[A, B, X, Y](ev: (A |*| B) =:= (X |*| Y)): (A =:= X, B =:= Y) =
        (ev.asInstanceOf[A =:= X], ev.asInstanceOf[B =:= Y])
    }

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
    case class AssocLR[A, B, C]() extends (((A |*| B) |*| C) -⚬ (A |*| (B |*| C)))
    case class AssocRL[A, B, C]() extends ((A |*| (B |*| C)) -⚬ ((A |*| B) |*| C))
    case class Swap[A, B]() extends ((A |*| B) -⚬ (B |*| A))
    case class InjectL[A, B]() extends (A -⚬ (A |+| B))
    case class InjectR[A, B]() extends (B -⚬ (A |+| B))
    case class EitherF[A, B, C](f: A -⚬ C, g: B -⚬ C) extends ((A |+| B) -⚬ C)
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
    case class MapVal[A, B](f: A => B) extends (Val[A] -⚬ Val[B])
    case class ConstVal[A](a: A) extends (Done -⚬ Val[A])
    case class ConstNeg[A](a: A) extends (Neg[A] -⚬ Need)
    case class Neglect[A]() extends (Val[A] -⚬ Done)
    case class NotifyVal[A]() extends (Val[A] -⚬ (Ping |*| Val[A]))
    case class NotifyNeg[A]() extends ((Pong |*| Neg[A]) -⚬ Neg[A])
    case class DebugPrint(msg: String) extends (Ping -⚬ One)

    case class Acquire[A, R, B](
      acquire: A => (R, B),
      release: Option[R => Unit],
    ) extends (Val[A] -⚬ (Res[R] |*| Val[B]))
    case class TryAcquireAsync[A, R, B, E](
      acquire: A => Async[Either[E, (R, B)]],
      release: Option[R => Async[Unit]],
    ) extends (Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])))
    case class Release[R]() extends (Res[R] -⚬ Done)
    case class ReleaseAsync[R, A, B](f: (R, A) => Async[B]) extends ((Res[R] |*| Val[A]) -⚬ Val[B])
    case class EffectAsync[R, A, B](f: (R, A) => Async[B]) extends ((Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]))
    case class EffectWrAsync[R, A](f: (R, A) => Async[Unit]) extends ((Res[R] |*| Val[A]) -⚬ Res[R])
    case class TryTransformResourceAsync[R, A, S, B, E](
      f: (R, A) => Async[Either[E, (S, B)]],
      release: Option[S => Async[Unit]],
    ) extends ((Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])))
    case class TrySplitResourceAsync[R, A, S, T, B, E](
      f: (R, A) => Async[Either[E, (S, T, B)]],
      release1: Option[S => Async[Unit]],
      release2: Option[T => Async[Unit]],
    ) extends ((Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])))

    case class Blocking[A, B](f: A => B) extends (Val[A] -⚬ Val[B])
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

  override def mapVal[A, B](f: A => B): Val[A] -⚬ Val[B] =
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
    acquire: A => (R, B),
    release: Option[R => Unit],
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    Acquire(acquire, release)

  override def tryAcquireAsync[A, R, B, E](
    acquire: A => Async[Either[E, (R, B)]],
    release: Option[R => Async[Unit]],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])) =
    TryAcquireAsync(acquire, release)

  override def release[R]: Res[R] -⚬ Done =
    Release()

  override def releaseAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ Val[B] =
    ReleaseAsync(f)

  override def effectAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    EffectAsync(f)

  override def effectWrAsync[R, A](f: (R, A) => Async[Unit]): (Res[R] |*| Val[A]) -⚬ Res[R] =
    EffectWrAsync(f)

  override def tryTransformResourceAsync[R, A, S, B, E](
    f: (R, A) => Async[Either[E, (S, B)]],
    release: Option[S => Async[Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    TryTransformResourceAsync(f, release)

  override def trySplitResourceAsync[R, A, S, T, B, E](
    f: (R, A) => Async[Either[E, (S, T, B)]],
    release1: Option[S => Async[Unit]],
    release2: Option[T => Async[Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])) =
    TrySplitResourceAsync(f, release1, release2)

  override def blocking[A, B](f: A => B): Val[A] -⚬ Val[B] =
    Blocking(f)

  override def forevert[A]: One -⚬ (-[A] |*| A) =
    Forevert()

  override def backvert[A]: (A |*| -[A]) -⚬ One =
    Backvert()

  override def distributeInversion[A, B]: -[A |*| B] -⚬ (-[A] |*| -[B]) =
    DistributeInversion()

  override def factorOutInversion[A, B]: (-[A] |*| -[B]) -⚬ -[A |*| B] =
    FactorOutInversion()

  implicit val cssc: ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬] =
    new ClosedSymmetricSemigroupalCategory[-⚬, |*|, =⚬] {
      override def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C                              = FreeScalaDSL.this.andThen(f, g)
      override def id[A]: A -⚬ A                                                               = FreeScalaDSL.this.id[A]
      override def par[A1, A2, B1, B2](f1: A1 -⚬ B1, f2: A2 -⚬ B2): (A1 |*| A2) -⚬ (B1 |*| B2) = FreeScalaDSL.this.par(f1, f2)
      override def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C))                    = FreeScalaDSL.this.assocLR[A, B, C]
      override def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C)                    = FreeScalaDSL.this.assocRL[A, B, C]
      override def swap[A, B]: (A |*| B) -⚬ (B |*| A)                                          = FreeScalaDSL.this.swap[A, B]
      override def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C)                            = FreeScalaDSL.this.curry(f)
      override def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B                                           = FreeScalaDSL.this.eval[A, B]
    }

  type Var[A] = libretto.impl.Var[VarOrigin, A]

  val closures: Closures[-⚬, |*|, =⚬, Var, Set[Var[?]]] =
    new Closures[-⚬, |*|, =⚬, Var, Set[Var[?]]]

  val lambdas: closures.lambdas.type =
    closures.lambdas

  override type $[A] = lambdas.Expr[A]

  override val `$`: ClosureOps  = new ClosureOps {
    override def map[A, B](a: $[A])(f: A -⚬ B)(
      pos: scalasource.Position,
    ): $[B] =
      (a map f)(new Var[B](VarOrigin.FunApp(pos)))

    override def zip[A, B](a: $[A], b: $[B])(
      pos: scalasource.Position,
    ): $[A |*| B] =
      (a zip b)(new Var[A |*| B](VarOrigin.Pairing(pos)))

    override def unzip[A, B](ab: $[A |*| B])(
      pos: scalasource.Position,
    ): ($[A], $[B]) =
      lambdas.Expr.unzip(ab)(
        new Var[A](VarOrigin.Prj1(pos)),
        new Var[B](VarOrigin.Prj2(pos)),
      )

    override def app[A, B](f: $[A =⚬ B], a: $[A])(
      pos: scalasource.Position,
    ): $[B] =
      closures.app(f, a)(new Var[B](VarOrigin.FunApp(pos)))
  }

  override def λ[A, B](f: $[A] => $[B])(implicit
    pos: scalasource.Position,
  ): A -⚬ B =
    lambdas.compile(f, boundVar = new Var[A](VarOrigin.Lambda(pos))) match {
      case Right(f) =>
        f
      case Left(e) =>
        import lambdas.Error.Undefined
        import lambdas.LinearityViolation.{Overused, Underused}
        e match {
          case Overused(vs)  => throw new NotLinearException(s"Variables used more than once: ${vs.toList.map(_.origin.print).mkString("\n", ", ", "\n")}")
          case Underused(vs) => throw new NotLinearException(s"Variables not fully consumed: ${vs.toList.map(_.origin.print).mkString("\n", ", ", "\n")}")
          case Undefined(vs) => throw new UnboundVariablesException(vs)
        }
    }

  override def Λ[A, B](f: $[A] => $[B])(implicit
    pos: scalasource.Position,
  ): $[A =⚬ B] =
    closures.closure[A, B](
      f,
      boundVar = new Var[A](VarOrigin.Lambda(pos)),
      resultVar = new Var[A =⚬ B](VarOrigin.ClosureVal(pos)),
    ) match {
      case Right(f) =>
        f
      case Left(e) =>
        import closures.ClosureError
        e match {
          case ClosureError.NonLinear(e) =>
            import lambdas.LinearityViolation.{Overused, Underused}
            e match {
              case Overused(vs)  => throw new NotLinearException(s"Variables used more than once: ${vs.toList.map(_.origin.print).mkString("\n", ", ", "\n")}")
              case Underused(vs) => throw new NotLinearException(s"Variables not fully consumed: ${vs.toList.map(_.origin.print).mkString("\n", ", ", "\n")}")
            }
          case ClosureError.NoCapture(msg) =>
            throw new NoCaptureException(msg)
        }
    }

  override class NotLinearException(msg: String) extends Exception(msg)
  override class UnboundVariablesException(vs: Set[Var[?]]) extends Exception
  override class NoCaptureException(msg: String) extends Exception
}
