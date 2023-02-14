package libretto.stream

import libretto.{InvertDSL, CoreLib}
import libretto.util.∀

object InvertStreams {
  def apply(
    dsl: InvertDSL,
    lib: CoreLib[dsl.type],
  )
  : InvertStreams[dsl.type, lib.type] =
    new InvertStreams(dsl, lib)
}

class InvertStreams[DSL <: InvertDSL, Lib <: CoreLib[DSL]](
  override val dsl: DSL,
  override val lib: Lib with CoreLib[dsl.type],
) extends CoreStreams[DSL, Lib](dsl, lib) {
  import dsl._
  import lib._

  type Drain[A] = StreamLeader[Need, -[A]]
  type Sink[A]  = StreamFollower[Need, -[A]]

  type LSubscriber[A] = StreamLeader[Need, A]
  type LDemanding[A] = Need |&| (A |*| LSubscriber[A])

  object LSubscriber {
    def unpack[A]: LSubscriber[A] -⚬ (Need |+| (Need |&| (A |*| LSubscriber[A]))) =
      dsl.unpack

    def pack[A]: (Need |+| (Need |&| (A |*| LSubscriber[A]))) -⚬ LSubscriber[A] =
      dsl.pack[StreamLeaderF[Need, A, _]]

    def unsubscribed[A]: Need -⚬ LSubscriber[A] =
      injectL > pack

    def close[A]: LSubscriber[A] -⚬ Need =
      unpack > either(id, chooseL)

    def switch[A, R](
      onDemand      : LDemanding[A] -⚬ R,
      onUnsubscribe :          Need -⚬ R,
    ): LSubscriber[A] -⚬ R =
      unpack > either(onUnsubscribe, onDemand)

    private def positiveLSubscriberF[A, X](implicit A: Junction.Negative[A]): SignalingJunction.Positive[StreamLeaderF[Need, A, X]] =
      SignalingJunction.Positive.eitherNeg(
        Junction.Negative.junctionNeed,
        Junction.Negative.delayChoice(
          Junction.Negative.junctionNeed,
          Junction.Negative.byFst(A),
        ),
      )

    implicit def universalPositiveLSubscriberF[A](implicit A: Junction.Negative[A]): ∀[λ[x => SignalingJunction.Positive[StreamLeaderF[Need, A, x]]]] =
      new ∀[λ[x => SignalingJunction.Positive[StreamLeaderF[Need, A, x]]]] {
        def apply[X]: SignalingJunction.Positive[StreamLeaderF[Need, A, X]] =
          positiveLSubscriberF[A, X]
      }

    implicit def positiveLSubscriber[A](implicit A: Junction.Negative[A]): SignalingJunction.Positive[LSubscriber[A]] =
      SignalingJunction.Positive.rec[StreamLeaderF[Need, A, _]](universalPositiveLSubscriberF)

    implicit def nAffineLSubscriber[A]: NAffine[LSubscriber[A]] =
      NAffine.from(LSubscriber.close)
  }

  object LDemanding {
    def exposeDemand[A]: LDemanding[A] -⚬ (A |*| LSubscriber[A]) =
      chooseR

    def supply[A, B](rInvert: (A |*| B) -⚬ One): (A |*| LDemanding[B]) -⚬ (Need |+| LDemanding[B]) =
      id                                 [  A |*|  LDemanding[B]           ]
        .>.snd(exposeDemand)          .to[  A |*| (B  |*| LSubscriber[B])  ]
        .assocRL                      .to[ (A |*|  B) |*| LSubscriber[B]   ]
        .elimFst(rInvert)             .to[                LSubscriber[B]   ]
        .>(LSubscriber.unpack)        .to[          Need |+| LDemanding[B] ]

    implicit def negativeLDemanding[A](implicit A: Junction.Negative[A]): SignalingJunction.Negative[LDemanding[A]] =
      SignalingJunction.Negative.choiceNeg(
        SignalingJunction.Negative.signalingJunctionNegativeNeed,
        Junction.Negative.byFst(A),
      )
  }

  def rInvertLSubscriber[A, B](
    rInvertElem: (A |*| B) -⚬ One,
  ): (LSubscriber[A] |*| LPollable[B]) -⚬ One =
    rInvertLeader(swap > rInvertSignal, rInvertElem)

  def lInvertLPollable[A, B](
    lInvertElem: One -⚬ (A |*| B),
  ): One -⚬ (LPollable[A] |*| LSubscriber[B]) =
    lInvertFollower[Done, Need, A, B](lInvertSignal > swap, lInvertElem)

  given subscriberPollableDuality[A, B](using AB: Dual[A, B]): Dual[LSubscriber[A], LPollable[B]] =
    leaderFollowerDuality[Need, Done, A, B](using dualSymmetric(doneNeedDuality))

  given pollableSubscriberDuality[A, B](using BA: Dual[B, A]): Dual[LPollable[A], LSubscriber[B]] =
    dualSymmetric(subscriberPollableDuality[B, A])
}
