package libretto.impl

import libretto.ScalaDSL

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
  override final class |*|[A, B] private()
  override final class |+|[A, B] private()
  override final class |&|[A, B] private()
  override final class Rec[F[_]] private()
  override final class Val[A] private()
  override final class Neg[A] private()
  
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
    case class DelayIndefinitely() extends (Done -⚬ Done)
    case class RegressInfinitely() extends (Need -⚬ Need)
    case class Fork() extends (Done -⚬ (Done |*| Done))
    case class Join() extends ((Done |*| Done) -⚬ Done)
    case class ForkNeed() extends ((Need |*| Need) -⚬ Need)
    case class JoinNeed() extends (Need -⚬ (Need |*| Need))
    case class SignalEither[A, B]() extends ((A |+| B) -⚬ (Done |*| (A |+| B)))
    case class SignalChoice[A, B]() extends ((Need |*| (A |&| B)) -⚬ (A |&| B))
    case class InjectLWhenDone[A, B]() extends ((Done |*| A) -⚬ (Done |*| (A |+| B)))
    case class InjectRWhenDone[A, B]() extends ((Done |*| B) -⚬ (Done |*| (A |+| B)))
    case class ChooseLWhenNeed[A, B]() extends ((Need |*| (A |&| B)) -⚬ (Need |*| A))
    case class ChooseRWhenNeed[A, B]() extends ((Need |*| (A |&| B)) -⚬ (Need |*| B))
    case class DistributeLR[A, B, C]() extends ((A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)))
    case class DistributeRL[A, B, C]() extends (((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C)))
    case class CoDistributeL[A, B, C]() extends (((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)))
    case class CoDistributeR[A, B, C]() extends (((A |*| C) |&| (B |*| C)) -⚬ ((A |&| B) |*| C))
    case class RInvertSignal() extends ((Done |*| Need) -⚬ One)
    case class LInvertSignal() extends (One -⚬ (Need |*| Done))
    case class RecF[A, B](f: (A -⚬ B) => (A -⚬ B)) extends (A -⚬ B) { self =>
      val recursed: A -⚬ B = f(self)
    }
    case class Pack[F[_]]() extends (F[Rec[F]] -⚬ Rec[F])
    case class Unpack[F[_]]() extends (Rec[F] -⚬ F[Rec[F]])
    case class RaceCompletion() extends ((Done |*| Done) -⚬ (Done |+| Done))
    case class SelectRequest() extends ((Need |&| Need) -⚬ (Need |*| Need))
    
    case class Promise[A]() extends (One -⚬ (Neg[A] |*| Val[A]))
    case class Fulfill[A]() extends ((Val[A] |*| Neg[A]) -⚬ One)
    case class LiftEither[A, B]() extends (Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]))
    case class UnliftEither[A, B]() extends ((Val[A] |+| Val[B]) -⚬ Val[Either[A, B]])
    case class LiftPair[A, B]() extends (Val[(A, B)] -⚬ (Val[A] |*| Val[B]))
    case class UnliftPair[A, B]() extends ((Val[A] |*| Val[B]) -⚬ Val[(A, B)])
    case class LiftNegPair[A, B]() extends (Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B]))
    case class UnliftNegPair[A, B]() extends ((Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)])
    case class LiftV[A, B](f: A => B) extends (Val[A] -⚬ Val[B])
    case class LiftN[A, B](f: A => B) extends (Neg[B] -⚬ Neg[A])
    case class ConstVal[A](a: A) extends (Done -⚬ Val[A])
    case class ConstNeg[A](a: A) extends (Neg[A] -⚬ Need)
    case class Neglect[A]() extends (Val[A] -⚬ Done)
    case class Inflate[A]() extends (Need -⚬ Neg[A])
  }
  
  import -⚬._

  def id[A]: A -⚬ A =
    Id()

  def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C =
    AndThen(f, g)

  def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D) =
    Par(f, g)

  def introFst[B]: B -⚬ (One |*| B) =
    IntroFst()
    
  def introSnd[A]: A -⚬ (A |*| One) =
    IntroSnd()
    
  def elimFst[B]: (One |*| B) -⚬ B =
    ElimFst()
    
  def elimSnd[A]: (A |*| One) -⚬ A =
    ElimSnd()

  def timesAssocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C)) =
    TimesAssocLR()
    
  def timesAssocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C) =
    TimesAssocRL()

  def swap[A, B]: (A |*| B) -⚬ (B |*| A) =
    Swap()

  def injectL[A, B]: A -⚬ (A |+| B) =
    InjectL()
    
  def injectR[A, B]: B -⚬ (A |+| B) =
    InjectR()

  def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C =
    EitherF(f, g)

  def chooseL[A, B]: (A |&| B) -⚬ A =
    ChooseL()
    
  def chooseR[A, B]: (A |&| B) -⚬ B =
    ChooseR()

  def choice[A, B, C](f: A -⚬ B, g: A -⚬ C): A -⚬ (B |&| C) =
    Choice(f, g)

  def done: One -⚬ Done =
    DoneF()
  
  def need: Need -⚬ One =
    NeedF()

  def delayIndefinitely: Done -⚬ Done =
    DelayIndefinitely()
    
  def regressInfinitely: Need -⚬ Need =
    RegressInfinitely()

  def fork: Done -⚬ (Done |*| Done) =
    Fork()
    
  def join: (Done |*| Done) -⚬ Done =
    Join()

  def forkNeed: (Need |*| Need) -⚬ Need =
    ForkNeed()
    
  def joinNeed: Need -⚬ (Need |*| Need) =
    JoinNeed()

  def signalEither[A, B]: (A |+| B) -⚬ (Done |*| (A |+| B)) =
    SignalEither()
    
  def signalChoice[A, B]: (Need |*| (A |&| B)) -⚬ (A |&| B) =
    SignalChoice()
    
  def injectLWhenDone[A, B]: (Done |*| A) -⚬ (Done |*| (A |+| B)) =
    InjectLWhenDone()
    
  def injectRWhenDone[A, B]: (Done |*| B) -⚬ (Done |*| (A |+| B)) =
    InjectRWhenDone()

  def chooseLWhenNeed[A, B]: (Need |*| (A |&| B)) -⚬ (Need |*| A) =
    ChooseLWhenNeed()
    
  def chooseRWhenNeed[A, B]: (Need |*| (A |&| B)) -⚬ (Need |*| B) =
    ChooseRWhenNeed()
    
  def distributeLR[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C)) =
    DistributeLR()
    
  def distributeRL[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C)) =
    DistributeRL()
    
  def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C)) =
    CoDistributeL()
    
  def coDistributeR[A, B, C]: ((A |*| C) |&| (B |*| C)) -⚬ ((A |&| B) |*| C) =
    CoDistributeR()
    
  def rInvertSignal: (Done |*| Need) -⚬ One =
    RInvertSignal()
    
  def lInvertSignal: One -⚬ (Need |*| Done) =
    LInvertSignal()

  def rec[A, B](f: (A -⚬ B) => (A -⚬ B)): A -⚬ B =
    RecF(f)
    
  def unpack[F[_]]: Rec[F] -⚬ F[Rec[F]] =
    Unpack()
    
  def pack[F[_]]: F[Rec[F]] -⚬ Rec[F] =
    Pack()
    
  def raceCompletion: (Done |*| Done) -⚬ (Done |+| Done) =
    RaceCompletion()
    
  def selectRequest: (Need |&| Need) -⚬ (Need |*| Need) =
    SelectRequest()

  def promise[A]: One -⚬ (Neg[A] |*| Val[A]) =
    Promise()
    
  def fulfill[A]: (Val[A] |*| Neg[A]) -⚬ One =
    Fulfill()

  def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B]) =
    LiftEither()
    
  def unliftEither[A, B]: (Val[A] |+| Val[B]) -⚬ Val[Either[A, B]] =
    UnliftEither()

  def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B]) =
    LiftPair()
    
  def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)] =
    UnliftPair()

  def liftNegPair[A, B]: Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B]) =
    LiftNegPair()
    
  def unliftNegPair[A, B]: (Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)] =
    UnliftNegPair()

  def liftV[A, B](f: A => B): Val[A] -⚬ Val[B] =
    LiftV(f)

  def liftN[A, B](f: A => B): Neg[B] -⚬ Neg[A] =
    LiftN(f)

  def constVal[A](a: A): Done -⚬ Val[A] =
    ConstVal(a)
    
  def constNeg[A](a: A): Neg[A] -⚬ Need =
    ConstNeg(a)

  def neglect[A]: Val[A] -⚬ Done =
    Neglect()
    
  def inflate[A]: Need -⚬ Neg[A] =
    Inflate()
}
