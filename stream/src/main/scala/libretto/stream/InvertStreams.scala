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
  import dsl.$._
  import lib._

  type Drain[A] = StreamLeader[Need, -[A]]
  type Sink[A]  = StreamFollower[Need, -[A]]

  object Drain {
    type Pulling[A] = Need |&| (-[A] |*| Drain[A])

    def close[A]: Drain[A] -⚬ Need =
      StreamLeader.switch(id, chooseL)

    def closed[A]: Need -⚬ Drain[A] =
      StreamLeader.closed[Need, -[A]]

    def pulling[A]: Pulling[A] -⚬ Drain[A] =
      StreamLeader.next[Need, -[A]]

    def switch[A, R](
      onClose: Need -⚬ R,
      onPull: Pulling[A] -⚬ R,
    ): Drain[A] -⚬ R =
      StreamLeader.switch(onClose, onPull)

    def toEither[A]: Drain[A] -⚬ (Need |+| Pulling[A]) =
      StreamLeader.unpack

    def fromEither[A]: (Need |+| Pulling[A]) -⚬ Drain[A] =
      StreamLeader.pack

    def onCloseAwait[A]: (Done |*| Drain[A]) -⚬ Drain[A] = rec { self =>
      λ { case (d |*| drain) =>
        toEither(drain) switch {
          case Left(closing) =>
            Drain.closed(needAbsorbDone(closing |*| d))
          case Right(pulling) =>
            Drain.pulling(Pulling.onCloseAwait0(self)(d |*| pulling))
        }
      }
    }

    object Pulling {
      def create[S, A](
        caseClose:    S -⚬ Need,
        caseWarrant:  S -⚬ (-[A] |*| Drain[A]),
      ): S -⚬ Pulling[A] =
        choice(caseClose, caseWarrant)

      def close[A]: Pulling[A] -⚬ Need =
        chooseL

      def warrant[A]: Pulling[A] -⚬ (-[A] |*| Drain[A]) =
        chooseR

      private[Drain] def onCloseAwait0[A](
        drainAwait: (Done |*| Drain[A]) -⚬ Drain[A],
      ): (Done |*| Pulling[A]) -⚬ Pulling[A] =
        create(
          caseClose   = λ { case (d |*| p) => needAbsorbDone(close(p) |*| d) },
          caseWarrant = snd(warrant) > XI > snd(drainAwait),
        )
    }

    private def needAbsorbDone: (Need |*| Done) -⚬ Need =
      fst(joinNeed) > assocLR > elimSnd(swap > rInvertSignal)
  }

  def rInvertDrain[A]: (Drain[A] |*| LPollable[A]) -⚬ One =
    rInvertLeader(swap > rInvertSignal, swap > backvert)

  def lInvertSource[A]: One -⚬ (LPollable[A] |*| Drain[A]) =
    lInvertFollower(lInvertSignal > swap, forevert > swap)

  given drainSourceDuality[A]: Dual[Drain[A], LPollable[A]] with {
    override val rInvert: (Drain[A] |*| LPollable[A]) -⚬ One = rInvertDrain
    override val lInvert: One -⚬ (LPollable[A] |*| Drain[A]) = lInvertSource
  }

  given sourceDrainDuality[A]: Dual[LPollable[A], Drain[A]] =
    dualSymmetric(drainSourceDuality[A])

  type LSubscriber[A] = StreamLeader[Need, A]
  type LDemanding[A] = Need |&| (A |*| LSubscriber[A])

  @deprecated
  object LSubscriber {
    def unpack[A]: LSubscriber[A] -⚬ (Need |+| (Need |&| (A |*| LSubscriber[A]))) =
      dsl.unpack

    def pack[A]: (Need |+| (Need |&| (A |*| LSubscriber[A]))) -⚬ LSubscriber[A] =
      dsl.pack[StreamLeaderF[Need, A, _]]

    def unsubscribed[A]: Need -⚬ LSubscriber[A] =
      injectL > pack

    def demanding[A]: LDemanding[A] -⚬ LSubscriber[A] =
      injectR > pack

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
