package libretto.scaletto.impl

import libretto.lambda.{DistributionNAry, SinkNAryNamed}
import libretto.lambda.Items1Named.Member
import libretto.lambda.util.Applicative
import scala.concurrent.duration.FiniteDuration

import phantoms.*

sealed trait Fun[+ ->[_, _], A, B] {
  import Fun.*

  def translateA[->>[_, _], G[_]](
    h: [X, Y] => (X -> Y) => G[X ->> Y],
  )(using
    G: Applicative[G],
  ): G[Fun[->>, A, B]] =
    this match
      case l: Leaf[A, B] => G.pure(l: Fun[->>, A, B])
      case AndThen(f, g) => G.map2(h(f), h(g)) { AndThen(_, _) }
      case Par(f1, f2) => G.map2(h(f1), h(f2)) { Par(_, _) }
      case EitherF(f, g) => G.map2(h(f), h(g)) { EitherF(_, _) }
      case OneOfHandle(hs) => G.map(hs.translateA[G, ->>]([x, y] => f => h(f))) { OneOfHandle(_) }
      case Choice(f, g) => G.map2(h(f), h(g)) { Choice(_, _) }
      case c: CaptureIntoSub[arr, x, a, b] => G.map2(h(c.discardCapture), h(c.splitCapture)) { CaptureIntoSub[->>, x, a, b](_, _) }
      case RecFun(f) => h(f).map { RecFun(_) }

  def foldMonoid[M](
    h: [X, Y] => (X -> Y) => M,
  )(using
    M: Monoid[M],
  ): M = {
    this match
      case _: Leaf[A, B] => M.unit
      case AndThen(f, g) => h(f) <> h(g)
      case Par(f1, f2) => h(f1) <> h(f2)
      case EitherF(f, g) => h(f) <> h(g)
      case OneOfHandle(hs) => hs.foldSemigroup([x, y] => f => h(f), M.combine)
      case Choice(f, g) => h(f) <> h(g)
      case CaptureIntoSub(dis, spl) => h(dis) <> h(spl)
      case RecFun(f) => h(f)
  }
}

object Fun {
  sealed trait Leaf[A, B] extends Fun[Nothing, A, B]

  case class AndThen[->[_, _], A, B, C](
    f: A -> B,
    g: B -> C,
  ) extends Fun[->, A, C]

  case class Par[->[_, _], A1, A2, B1, B2](
    f1: A1 -> B1,
    f2: A2 -> B2,
  ) extends Fun[->, A1 |*| A2, B1 |*| B2]

  case class EitherF[->[_, _], A, B, C](
    f: A -> C,
    g: B -> C,
  ) extends Fun[->, A |+| B, C]

  case class OneOfHandle[->[_, _], Cases, R](
    handlers: SinkNAryNamed[->, ||, ::, Cases, R]
  ) extends Fun[->, OneOf[Cases], R]

  case class Choice[->[_, _], A, B, C](
    f: A -> B,
    g: A -> C,
  ) extends Fun[->, A, B |&| C]

  case class RecFun[->[_, _], A, B](
    f: (Sub[A, B] |*| A) -> B,
  ) extends Fun[->, A, B]

  case class CaptureIntoSub[->[_, _], X, A, B](
    discardCapture: X -> One,
    splitCapture: X -> (X |*| X),
  ) extends Fun[->, Sub[X |*| A, B] |*| X, Sub[A, B]]

  case class Id[A]() extends Leaf[A, A]
  case class IntroFst[B]() extends Leaf[B, One |*| B]
  case class IntroSnd[A]() extends Leaf[A, A |*| One]
  case class ElimFst[B]() extends Leaf[One |*| B, B]
  case class ElimSnd[A]() extends Leaf[A |*| One, A]
  case class AssocLR[A, B, C]() extends Leaf[(A |*| B) |*| C, A |*| (B |*| C)]
  case class AssocRL[A, B, C]() extends Leaf[A |*| (B |*| C), (A |*| B) |*| C]
  case class Swap[A, B]() extends Leaf[A |*| B, B |*| A]
  case class InjectL[A, B]() extends Leaf[A, A |+| B]
  case class InjectR[A, B]() extends Leaf[B, A |+| B]
  case class Absurd[A]() extends Leaf[Void, A]
  case class OneOfInject[Label, A, Cases](i: Member[||, ::, Label, A, Cases]) extends Leaf[A, OneOf[Cases]]
  case class ChooseL[A, B]() extends Leaf[A |&| B, A]
  case class ChooseR[A, B]() extends Leaf[A |&| B, B]
  case class PingF() extends Leaf[One, Ping]
  case class PongF() extends Leaf[Pong, One]
  case class DelayIndefinitely() extends Leaf[Done, RTerminus]
  case class RegressInfinitely() extends Leaf[LTerminus, Need]
  case class Fork() extends Leaf[Done, Done |*| Done]
  case class Join() extends Leaf[Done |*| Done, Done]
  case class ForkNeed() extends Leaf[Need |*| Need, Need]
  case class JoinNeed() extends Leaf[Need, Need |*| Need]
  case class NotifyDoneL() extends Leaf[Done, Ping |*| Done]
  case class NotifyNeedL() extends Leaf[Pong |*| Need, Need]
  case class ForkPing() extends Leaf[Ping, Ping |*| Ping]
  case class ForkPong() extends Leaf[Pong |*| Pong, Pong]
  case class JoinPing() extends Leaf[Ping |*| Ping, Ping]
  case class JoinPong() extends Leaf[Pong, Pong |*| Pong]
  case class StrengthenPing() extends Leaf[Ping, Done]
  case class StrengthenPong() extends Leaf[Need, Pong]
  case class JoinRTermini() extends Leaf[RTerminus |*| RTerminus, RTerminus]
  case class JoinLTermini() extends Leaf[LTerminus, LTerminus |*| LTerminus]
  case class NotifyEither[A, B]() extends Leaf[A |+| B, Ping |*| (A |+| B)]
  case class NotifyChoice[A, B]() extends Leaf[Pong |*| (A |&| B), A |&| B]
  case class InjectLOnPing[A, B]() extends Leaf[Ping |*| A, A |+| B]
  case class ChooseLOnPong[A, B]() extends Leaf[A |&| B, Pong |*| A]
  case class DistributeNAryLR[A, Cases, ACases](
    dist: DistributionNAry.DistLR[|*|, ||, ::, A, Cases] { type Out = ACases },
  ) extends Leaf[A |*| OneOf[Cases], OneOf[ACases]]
  case class DistributeNAryRL[B, Cases, BCases](
    dist: DistributionNAry.DistRL[|*|, ||, ::, B, Cases] { type Out = BCases },
  ) extends Leaf[OneOf[Cases] |*| B, OneOf[BCases]]
  case class DistributeL[A, B, C]() extends Leaf[A |*| (B |+| C), (A |*| B) |+| (A |*| C)]
  case class CoDistributeL[A, B, C]() extends Leaf[(A |*| B) |&| (A |*| C), A |*| (B |&| C)]
  case class RInvertSignal() extends Leaf[Done |*| Need, One]
  case class LInvertSignal() extends Leaf[One, Need |*| Done]
  case class RInvertPingPong() extends Leaf[Ping |*| Pong, One]
  case class LInvertPongPing() extends Leaf[One, Pong |*| Ping]
  case class RInvertTerminus() extends Leaf[RTerminus |*| LTerminus, One]
  case class LInvertTerminus() extends Leaf[One, LTerminus |*| RTerminus]
  case class InvokeSub[A, B]() extends Leaf[Sub[A, B] |*| A, B]
  case class IgnoreSub[A, B]() extends Leaf[Sub[A, B], One]
  case class DupSub[A, B]() extends Leaf[Sub[A, B], Sub[A, B] |*| Sub[A, B]]
  case class Pack[F[_]]() extends Leaf[F[Rec[F]], Rec[F]]
  case class Unpack[F[_]]() extends Leaf[Rec[F], F[Rec[F]]]
  case class RacePair() extends Leaf[Ping |*| Ping, One |+| One]
  case class SelectPair() extends Leaf[One |&| One, Pong |*| Pong]

  case class Forevert[A]() extends Leaf[One, -[A] |*| A]
  case class Backvert[A]() extends Leaf[A |*| -[A], One]
  case class DistributeInversion[A, B]() extends Leaf[-[A |*| B], -[A] |*| -[B]]
  case class FactorOutInversion[A, B]() extends Leaf[-[A] |*| -[B], -[A |*| B]]

  case class CrashWhenDone[A, B](msg: String) extends Leaf[Done |*| A, B]
  case class Delay() extends Leaf[Val[FiniteDuration], Done]
  case class LiftEither[A, B]() extends Leaf[Val[Either[A, B]], Val[A] |+| Val[B]]
  case class LiftPair[A, B]() extends Leaf[Val[(A, B)], Val[A] |*| Val[B]]
  case class UnliftPair[A, B]() extends Leaf[Val[A] |*| Val[B], Val[(A, B)]]
  case class MapVal[A, B](f: ScalaFunction[A, B]) extends Leaf[Val[A], Val[B]]
  case class ConstVal[A](a: A) extends Leaf[Done, Val[A]]
  case class ConstNeg[A](a: A) extends Leaf[-[Val[A]], Need]
  case class Neglect[A]() extends Leaf[Val[A], Done]
  case class NotifyVal[A]() extends Leaf[Val[A], Ping |*| Val[A]]
  case class NotifyNeg[A]() extends Leaf[Pong |*| -[Val[A]], -[Val[A]]]
  case class DebugPrint(msg: String) extends Leaf[Ping, One]

  case class Acquire[A, R, B](
    acquire: ScalaFunction[A, (R, B)],
    release: Option[ScalaFunction[R, Unit]],
  ) extends Leaf[Val[A], Res[R] |*| Val[B]]

  case class TryAcquire[A, R, B, E](
    acquire: ScalaFunction[A, Either[E, (R, B)]],
    release: Option[ScalaFunction[R, Unit]],
  ) extends Leaf[Val[A], Val[E] |+| (Res[R] |*| Val[B])]

  case class Release[R]() extends Leaf[Res[R], Done]
  case class ReleaseWith[R, A, B](f: ScalaFunction[(R, A), B]) extends Leaf[Res[R] |*| Val[A], Val[B]]
  case class Effect[R, A, B](f: ScalaFunction[(R, A), B]) extends Leaf[Res[R] |*| Val[A], Res[R] |*| Val[B]]
  case class EffectWr[R, A](f: ScalaFunction[(R, A), Unit]) extends Leaf[Res[R] |*| Val[A], Res[R]]

  case class TryEffectAcquire[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ) extends Leaf[Res[R] |*| Val[A], Res[R] |*| (Val[E] |+| (Res[S] |*| Val[B]))]

  case class TryTransformResource[R, A, S, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFunction[S, Unit]],
  ) extends Leaf[Res[R] |*| Val[A], Val[E] |+| (Res[S] |*| Val[B])]

  case class TrySplitResource[R, A, S, T, B, E](
    f: ScalaFunction[(R, A), Either[E, (S, T, B)]],
    release1: Option[ScalaFunction[S, Unit]],
    release2: Option[ScalaFunction[T, Unit]],
  ) extends Leaf[Res[R] |*| Val[A], Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])]
}
