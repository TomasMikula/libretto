package libretto

object CoreStreams {
  def apply(
    dsl: CoreDSL,
    lib: CoreLib[dsl.type],
  )
  : CoreStreams[dsl.type, lib.type] =
    new CoreStreams(dsl, lib)
}

class CoreStreams[DSL <: CoreDSL, Lib <: CoreLib[DSL]](
  val dsl: DSL,
  val lib: Lib with CoreLib[dsl.type],
) {
  import dsl._
  import lib._

  type LPollableF[A, X] = Done |&| (Done |+| (A |*| X))
  type LPollable[A] = Rec[LPollableF[A, *]]
  type LPolled[A] = Done |+| (A |*| LPollable[A])

  type LSubscriberF[A, X]  = Need |+| (Need |&| (A |*| X))
  type LSubscriber[A] = Rec[LSubscriberF[A, *]]
  type LDemanding[A] = Need |&| (A |*| LSubscriber[A])

  object LPollable {
    def pack[A]: (Done |&| LPolled[A]) -⚬ LPollable[A] =
      dsl.pack[LPollableF[A, *]]

    def unpack[A]: LPollable[A] -⚬ (Done |&| LPolled[A]) =
      dsl.unpack[LPollableF[A, *]]

    def from[A, B](
      onClose: A -⚬ Done,
      onPoll: A -⚬ LPolled[B],
    ): A -⚬ LPollable[B] =
      choice(onClose, onPoll) >>> pack

    def close[A]: LPollable[A] -⚬ Done =
      id                       [    LPollable[A]     ]
        .unpack             .to[ Done |&| LPolled[A] ]
        .chooseL            .to[ Done                ]

    def poll[A]: LPollable[A] -⚬ LPolled[A] =
      id                       [    LPollable[A]     ]
        .unpack             .to[ Done |&| LPolled[A] ]
        .chooseR            .to[          LPolled[A] ]

    def delayedPoll[A: Junction.Positive]: (Done |*| LPollable[A]) -⚬ LPolled[A] =
      id                                       [ Done |*|     LPollable[A]      ]
        .>.snd(unpack)                      .to[ Done |*| (Done |&| LPolled[A]) ]
        .>(chooseRWhenDone)                 .to[ Done |*|           LPolled[A]  ]
        .>(LPolled.delayBy[A])              .to[                    LPolled[A]  ]

    /** Polls and discards all elements. */
    def drain[A](implicit A: PComonoid[A]): LPollable[A] -⚬ Done =
      rec { self =>
        poll[A] > either(id, join(A.counit, self))
      }

    def emptyF[A]: Done -⚬ LPollableF[A, LPollable[A]] =
      choice[Done, Done, LPolled[A]](id, injectL)

    def empty[A]: Done -⚬ LPollable[A] =
      emptyF[A].pack

    def cons[A](implicit A: PAffine[A]): (A |*| LPollable[A]) -⚬ LPollable[A] = {
      val onClose: (A |*| LPollable[A]) -⚬ Done       = join(A.neglect, LPollable.close)
      val onPoll:  (A |*| LPollable[A]) -⚬ LPolled[A] = LPolled.cons
      from(onClose, onPoll)
    }

    def fromLList[A](implicit A: PAffine[A]): LList[A] -⚬ LPollable[A] = rec { self =>
      LList.switch(
        caseNil  = done          >>> LPollable.empty[A],
        caseCons = par(id, self) >>> LPollable.cons[A],
      )
    }

    def of[A](as: (One -⚬ A)*)(implicit A: PAffine[A]): One -⚬ LPollable[A] =
      LList.of(as: _*) >>> fromLList

    def repeatedly[A](f: Done -⚬ A): Done -⚬ LPollable[A] = rec { self =>
      from(
        onClose = id[Done],
        onPoll = fork(f, self) > LPolled.cons,
      )
    }

    /** Signals the first action (i.e. [[poll]] or [[close]]) via a negative (i.e. [[Need]]) signal. */
    def signalAction[A]: (Need |*| LPollable[A]) -⚬ LPollable[A] =
      id                             [             LPollable[A]       ]
        .<(pack)                .from[           Done |&| LPolled[A]  ]
        .<(signalChoice)        .from[ Need |*| (Done |&| LPolled[A]) ]
        .<.snd(unpack)          .from[ Need |*|    LPollable[A]       ]

    /** Delays the first action ([[poll]] or [[close]]) until the [[Done]] signal completes. */
    def delayBy[A](implicit ev: Junction.Positive[A]): (Done |*| LPollable[A]) -⚬ LPollable[A] =
      id                                           [  Done |*|     LPollable[A]                 ]
        .>.snd(unpack)                          .to[  Done |*| (Done  |&|           LPolled[A]) ]
        .>(delayChoiceUntilDone)                .to[ (Done |*|  Done) |&| (Done |*| LPolled[A]) ]
        .bimap(join, LPolled.delayBy[A])        .to[       Done       |&|           LPolled[A]  ]
        .pack[LPollableF[A, *]]                 .to[              LPollable[A]                  ]

    /** Delays the final [[Done]] signal (signaling end of stream or completed [[close]]) until the given [[Done]]
      * signal completes.
      */
    def delayClosedBy[A]: (Done |*| LPollable[A]) -⚬ LPollable[A] = rec { self =>
      id                                               [  Done |*|     LPollable[A]                 ]
        .>.snd(unpack)                              .to[  Done |*| (Done  |&|           LPolled[A]) ]
        .>(coFactorL)                               .to[ (Done |*|  Done) |&| (Done |*| LPolled[A]) ]
        .bimap(join, LPolled.delayClosedBy(self))   .to[       Done       |&|           LPolled[A]  ]
        .pack[LPollableF[A, *]]                     .to[              LPollable[A]                  ]
    }

    /** Delays the first action ([[poll]] or [[close]]) on this [[LPollable]]. */
    def delay[A: Junction.Positive]: LPollable[A] -⚬ Delayed[LPollable[A]] =
      Delayed.from(delayBy)

    /** Delays the final [[Done]] signal resulting from [[close]] or end of stream. */
    def delayClosed[A]: LPollable[A] -⚬ Delayed[LPollable[A]] =
      Delayed.from(delayClosedBy)

    def map[A, B](f: A -⚬ B): LPollable[A] -⚬ LPollable[B] = rec { self =>
      from(close[A], poll[A].>.right(par(f, self)))
    }

    def forEachSequentially[A: Junction.Positive](f: A -⚬ Done): LPollable[A] -⚬ Done = rec { self =>
      val caseCons: (A |*| LPollable[A]) -⚬ Done =
        par(f, id) > LPollable.delayBy[A] > self

      poll[A] > LPolled.switch(caseEmpty = id[Done], caseCons)
    }

    /** The second [[LPollable]] is "delayed" because that gives flexibility in how the [[Done]] signal resulting from
      * the exhaustion of the first [[LPollable]] is awaited. For example, if polling of the second [[LPollable]]
      * should be delayed until the first [[LPollable]] is completely shut down, we can use [[delay]] to delay the
      * second [[LPollable]]. If polling of the second [[LPollable]] should start as soon as it is known that there are
      * no more elements in the first [[LPollable]], we can use [[delayClosed]] to delay the second [[LPollable]].
      */
    def concatenate[A]: (LPollable[A] |*| Delayed[LPollable[A]]) -⚬ LPollable[A] = rec { self =>
      val close: (LPollable[A] |*| Delayed[LPollable[A]]) -⚬ Done =
        join(LPollable.close, Delayed.force >>> LPollable.close)

      val poll: (LPollable[A] |*| Delayed[LPollable[A]]) -⚬ LPolled[A] =
        id                               [                                               LPollable[A]    |*| Delayed[LPollable[A]]   ]
          .>.fst(unpack)              .to[ (Done |&| (Done                  |+|  (A |*|  LPollable[A]))) |*| Delayed[LPollable[A]]   ]
          .>.fst(chooseR)             .to[           (Done                  |+|  (A |*|  LPollable[A]))  |*| Delayed[LPollable[A]]   ]
          .distributeR                .to[ (Done |*| Delayed[LPollable[A]]) |+| ((A |*|  LPollable[A])   |*| Delayed[LPollable[A]] ) ]
          .>.left(Delayed.triggerBy)  .to[                   LPollable[A]   |+| ((A |*|  LPollable[A])   |*| Delayed[LPollable[A]] ) ]
          .>.left(LPollable.poll)     .to[                     LPolled[A]   |+| ((A |*|  LPollable[A])   |*| Delayed[LPollable[A]] ) ]
          .>.right(timesAssocLR)      .to[                     LPolled[A]   |+| ( A |*| (LPollable[A]    |*| Delayed[LPollable[A]])) ]
          .>.right.snd(self)          .to[                     LPolled[A]   |+| ( A |*|            LPollable[A]                    ) ]
          .>.right.injectR[Done]      .to[                     LPolled[A]   |+|     LPolled[A]                                       ]
          .>(either(id, id))          .to[                              LPolled[A]                                                   ]

      from(close, poll)
    }

    def concat[A]: (LPollable[A] |*| LPollable[A]) -⚬ LPollable[A] =
      id.>.snd(delayClosed) >>> concatenate

    /** Splits a stream of "`A` or `B`" to a stream of `A` and a stream of `B`.
      *
      * Polls the upstream only after ''both'' downstreams poll.
      * When either of the downstreams closes, the other downstream and the upstream are closed as well.
      */
    def partition[A, B]: LPollable[A |+| B] -⚬ (LPollable[A] |*| LPollable[B]) = rec { self =>
      val fstClosed: LPollable[A |+| B] -⚬ (Done |*| LPollable[B]) =
        close[A |+| B].introSnd(done >>> empty[B])

      val sndClosed: LPollable[A |+| B] -⚬ (LPolled[A] |*| Done) =
        close[A |+| B].introFst(done >>> LPolled.empty[A])

      val bothPolled: LPollable[A |+| B] -⚬ (LPolled[A] |*| LPolled[B]) = {
        val upClosed: Done -⚬ (LPolled[A] |*| LPolled[B]) =
          fork(LPolled.empty[A], LPolled.empty[B])

        val upValue: ((A |+| B) |*| LPollable[A |+| B]) -⚬ (LPolled[A] |*| LPolled[B]) =
          id                                 [ (A                                      |+|  B) |*|         LPollable[A |+| B]       ]
            .>.snd(self)                  .to[ (A                                      |+|  B) |*| (LPollable[A] |*| LPollable[B])  ]
            .distributeR                  .to[ (A |*| (LPollable[A] |*| LPollable[B])) |+| (B  |*| (LPollable[A] |*| LPollable[B])) ]
            .>.left(timesAssocRL)         .to[ ((A |*| LPollable[A]) |*| LPollable[B]) |+| (B  |*| (LPollable[A] |*| LPollable[B])) ]
            .>.right(XI)                  .to[ ((A |*| LPollable[A]) |*| LPollable[B]) |+| (LPollable[A] |*|  (B |*| LPollable[B])) ]
            .> .left.fst(LPolled.cons)    .to[ (  LPolled[A]         |*| LPollable[B]) |+| (LPollable[A] |*|  (B |*| LPollable[B])) ]
            .>.right.snd(LPolled.cons)    .to[ (  LPolled[A]         |*| LPollable[B]) |+| (LPollable[A] |*|    LPolled[B]        ) ]
            .> .left.snd(poll)            .to[ (  LPolled[A]         |*|   LPolled[B]) |+| (LPollable[A] |*|    LPolled[B]        ) ]
            .>.right.fst(poll)            .to[ (  LPolled[A]         |*|   LPolled[B]) |+| (  LPolled[A] |*|    LPolled[B]        ) ]
            .either(id, id)

        id                                   [   LPollable[A |+| B]                        ]
          .>(poll)                        .to[ Done |+| ((A |+| B) |*| LPollable[A |+| B]) ]
          .either(upClosed, upValue)      .to[         LPolled[A] |*| LPolled[B]           ]
      }

      val fstPolled: LPollable[A |+| B] -⚬ (LPolled[A] |*| LPollable[B]) =
        id                                   [                 LPollable[A |+| B]                    ]
          .choice(sndClosed, bothPolled)  .to[ (LPolled[A] |*| Done) |&| (LPolled[A] |*| LPolled[B]) ]
          .coDistributeL                  .to[  LPolled[A] |*| (Done |&|                 LPolled[B]) ]
          .>.snd(pack)                    .to[  LPolled[A] |*|   LPollable[B]                        ]

      id                                 [                   LPollable[A |+| B]                      ]
        .choice(fstClosed, fstPolled) .to[ (Done |*| LPollable[B]) |&| (LPolled[A] |*| LPollable[B]) ]
        .coDistributeR                .to[ (Done                   |&| LPolled[A]) |*| LPollable[B]  ]
        .>.fst(pack)                  .to[                     LPollable[A]        |*| LPollable[B]  ]
    }

    /** Merges two [[LPollable]]s into one.
      * Left-biased: when there is a value available from both upstreams, favors the first one.
      */
    def merge[A](implicit
      A1: Junction.Positive[A],
      A2: PComonoid[A],
    ): (LPollable[A] |*| LPollable[A]) -⚬ LPollable[A] = rec { self =>
      val onClose: (LPollable[A] |*| LPollable[A]) -⚬ Done       = join(close, close)
      val onPoll : (LPollable[A] |*| LPollable[A]) -⚬ LPolled[A] = par(poll, poll) >>> LPolled.merge(self)
      from(onClose, onPoll)
    }

    /** Merges a list of [[LPollable]]s into a single [[LPollable]].
      * Head-biased: when there is an element available from multiple upstreams, favors the upstream closest to the
      * head of the input list.
      */
    def mergeAll[A](implicit
      A1: Junction.Positive[A],
      A2: PComonoid[A],
    ): LList[LPollable[A]] -⚬ LPollable[A] =
      rec { self =>
        LList.switch(
          caseNil = done >>> LPollable.empty,
          caseCons = par(id, self) >>> merge,
        )
      }

    implicit def positiveJunction[A](implicit A: Junction.Positive[A]): Junction.Positive[LPollable[A]] =
      Junction.Positive.from(LPollable.delayBy)

    implicit def negativeSignaling[A]: Signaling.Negative[LPollable[A]] =
      Signaling.Negative.from(LPollable.signalAction[A])

    implicit def negativeLPollable[A](implicit A: Junction.Positive[A]): SignalingJunction.Negative[LPollable[A]] =
      SignalingJunction.Negative.from(
        negativeSignaling,
        Junction.invert(positiveJunction),
      )

    implicit def pAffineLPollable[A]: PAffine[LPollable[A]] =
      PAffine.from(LPollable.close)
  }

  object LPolled {
    def close[A](neglect: A -⚬ Done): LPolled[A] -⚬ Done =
      either(id, join(neglect, LPollable.close))

    def empty[A]: Done -⚬ LPolled[A] =
      injectL

    def cons[A]: (A |*| LPollable[A]) -⚬ LPolled[A] =
      injectR

    def switch[A, R](
      caseEmpty: Done -⚬ R,
      caseCons: (A |*| LPollable[A]) -⚬ R,
    ): LPolled[A] -⚬ R = {
      either(caseEmpty, caseCons)
    }

    def unpoll[A](implicit A: PComonoid[A]): LPolled[A] -⚬ LPollable[A] =
      LPollable.from(close(A.counit), id)

    def delayBy[A](implicit ev: Junction.Positive[A]): (Done |*| LPolled[A]) -⚬ LPolled[A] =
      id[Done |*| LPolled[A]]         .to[  Done |*| (Done |+|           (A |*| LPollable[A])) ]
        .distributeL                  .to[ (Done |*| Done) |+| (Done |*| (A |*| LPollable[A])) ]
        .>.left(join)                 .to[      Done       |+| (Done |*| (A |*| LPollable[A])) ]
        .>.right(timesAssocRL)        .to[      Done       |+| ((Done |*| A) |*| LPollable[A]) ]
        .>.right.fst(ev.awaitPosFst)  .to[      Done       |+| (          A  |*| LPollable[A]) ]

    def delayClosedBy[A](
      delayLPollableClosed: (Done |*| LPollable[A]) -⚬ LPollable[A],
    ): (Done |*| LPolled[A]) -⚬ LPolled[A] =
      id[Done |*| LPolled[A]]               .to[  Done |*| (Done |+|           (A |*| LPollable[A])) ]
        .distributeL                        .to[ (Done |*| Done) |+| (Done |*| (A |*| LPollable[A])) ]
        .>.left(join)                       .to[      Done       |+| (Done |*| (A |*| LPollable[A])) ]
        .>.right(XI)                        .to[      Done       |+| (A |*| (Done |*| LPollable[A])) ]
        .>.right.snd(delayLPollableClosed)  .to[      Done       |+| (A |*|           LPollable[A] ) ]

    def feedTo[A, B](
      f: (A |*| B) -⚬ PMaybe[B],
    ): (LPolled[A] |*| B) -⚬ (Done |*| Maybe[B]) = rec { self =>
      val upstreamValue: ((A |*| LPollable[A]) |*| B) -⚬ (Done |*| Maybe[B]) = {
        val caseStop: (LPollable[A] |*| Done) -⚬ (Done |*| Maybe[B]) =
          join(LPollable.close, id) > introSnd(Maybe.empty[B])
        val caseCont: (LPollable[A] |*| B) -⚬ (Done |*| Maybe[B]) =
          par(LPollable.poll, id) > self
        id                                             [ (     A       |*| LPollable[A]) |*| B  ]
          .>.fst(swap)                              .to[ (LPollable[A] |*|      A      ) |*| B  ]
          .assocLR                                  .to[  LPollable[A] |*| (    A        |*| B) ]
          .>.snd(f)                                 .to[  LPollable[A] |*|           PMaybe[B]  ]
          .>(PMaybe.switchWithL(caseStop, caseCont)).to[             Done |*| Maybe[B]          ]
      }

      val upstreamClosed: (Done |*| B) -⚬ (Done |*| Maybe[B]) =
        par(id, Maybe.just)

      id[ (Done |+| (A |*| LPollable[A])) |*| B ]
        .distributeR
        .either(upstreamClosed, upstreamValue)
    }

    implicit def positiveLPolled[A](implicit A: Junction.Positive[A]): SignalingJunction.Positive[LPolled[A]] =
      SignalingJunction.Positive.eitherPos(
        SignalingJunction.Positive.signalingJunctionPositiveDone,
        Junction.Positive.byFst(A),
      )

    /** Merges two [[LPolled]]s into one.
      * Left-biased: whenever there is a value available from both upstreams, favors the first one.
      *
      * @param mergePollables left-biased merge of two [[LPollable]]s.
      */
    def merge[A](
      mergePollables: (LPollable[A] |*| LPollable[A]) -⚬ LPollable[A],
    )(implicit
      A1: Junction.Positive[A],
      A2: PComonoid[A],
    ): (LPolled[A] |*| LPolled[A]) -⚬ LPolled[A] = {
      // checks the first argument first, uses the given function for recursive calls
      def go(merge: (LPollable[A] |*| LPollable[A]) -⚬ LPollable[A]): (LPolled[A] |*| LPolled[A]) -⚬ LPolled[A] =
        id[LPolled[A] |*| LPolled[A]] .to[ (Done                 |+|  (A |*| LPollable[A])) |*| LPolled[A]     ]
          .distributeR                .to[ (Done |*| LPolled[A]) |+| ((A |*| LPollable[A])  |*| LPolled[A]   ) ]
          .>.left(delayBy[A])         .to[           LPolled[A]  |+| ((A |*| LPollable[A])  |*| LPolled[A]   ) ]
          .>.right.snd(unpoll)        .to[           LPolled[A]  |+| ((A |*| LPollable[A])  |*| LPollable[A] ) ]
          .>.right.assocLR            .to[           LPolled[A]  |+| ( A |*| (LPollable[A]  |*| LPollable[A])) ]
          .>.right.snd(merge)         .to[           LPolled[A]  |+| ( A |*|           LPollable[A]          ) ]
          .>.right(cons)              .to[           LPolled[A]  |+|     LPolled[A]                            ]
          .either(id, id)             .to[                   LPolled[A]                                        ]

      // checks the first argument first
      val goFst: (LPolled[A] |*| LPolled[A]) -⚬ LPolled[A] = go(mergePollables)

      // checks the second argument first
      val goSnd: (LPolled[A] |*| LPolled[A]) -⚬ LPolled[A] =
        swap >>> go(swap >>> mergePollables)

      race(goFst, goSnd)
    }
  }

  object LSubscriber {
    def unsubscribed[A]: Need -⚬ LSubscriber[A] =
      injectL > pack[LSubscriberF[A, *]]

    def close[A]: LSubscriber[A] -⚬ Need =
      unpack[LSubscriberF[A, *]] >>> either(id, chooseL)

    def switch[A, R](
      onDemand      : LDemanding[A] -⚬ R,
      onUnsubscribe :          Need -⚬ R,
    ): LSubscriber[A] -⚬ R =
      unpack >>> either(onUnsubscribe, onDemand)

    implicit def positiveLSubscriberF[A, X](implicit A: Junction.Negative[A]): SignalingJunction.Positive[LSubscriberF[A, X]] =
      SignalingJunction.Positive.eitherNeg(
        Junction.Negative.junctionNeed,
        Junction.Negative.delayChoice(
          Junction.Negative.junctionNeed,
          Junction.Negative.byFst(A),
        ),
      )

    implicit def universalPositiveLSubscriberF[A](implicit A: Junction.Negative[A]): ∀[λ[x => SignalingJunction.Positive[LSubscriberF[A, x]]]] =
      new ∀[λ[x => SignalingJunction.Positive[LSubscriberF[A, x]]]] {
        def apply[X]: SignalingJunction.Positive[LSubscriberF[A, X]] =
          positiveLSubscriberF[A, X]
      }

    implicit def positiveLSubscriber[A](implicit A: Junction.Negative[A]): SignalingJunction.Positive[LSubscriber[A]] =
      SignalingJunction.Positive.rec[LSubscriberF[A, *]](universalPositiveLSubscriberF)

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
        .unpack[LSubscriberF[B, *]]   .to[          Need |+| LDemanding[B] ]

    implicit def negativeLDemanding[A](implicit A: Junction.Negative[A]): SignalingJunction.Negative[LDemanding[A]] =
      SignalingJunction.Negative.choiceNeg(
        SignalingJunction.Negative.signalingJunctionNegativeNeed,
        Junction.Negative.byFst(A),
      )
  }

  def rInvertLSubscriberF[A, B, x, y](
    rInvertA: (A |*| B) -⚬ One,
    rInvertSub: (x |*| y) -⚬ One,
  ): (LSubscriberF[B, y] |*| LPollableF[A, x]) -⚬ One =
    rInvertEither(
      swap >>> rInvertSignal,
      swap >>> rInvertEither(
        rInvertSignal,
        rInvertTimes(
          rInvertA,
          rInvertSub
        )
      )
    )

  def rInvertLSubscriber[A, B](
    rInvertElem: (A |*| B) -⚬ One,
  ): (LSubscriber[B] |*| LPollable[A]) -⚬ One =
    rInvertRec[LSubscriberF[B, *], LPollableF[A, *]](
      [X, Y] => (rInvertSub: (X |*| Y) -⚬ One) =>
        rInvertLSubscriberF(rInvertElem, swap >>> rInvertSub)
    )

  def lInvertLPollableF[A, B, x, y](
    lInvertA: One -⚬ (B |*| A),
    lInvertSub: One -⚬ (y |*| x),
  ): One -⚬ (LPollableF[A, x] |*| LSubscriberF[B, y]) =
    lInvertChoice(
      lInvertSignal >>> swap,
      lInvertChoice(
        lInvertSignal,
        lInvertTimes(
          lInvertA,
          lInvertSub
        )
      ) >>> swap
    )

  def lInvertLPollable[A, B](
    lInvertElem: One -⚬ (B |*| A),
  ): One -⚬ (LPollable[A] |*| LSubscriber[B]) =
    lInvertRec[LPollableF[A, *], LSubscriberF[B, *]](
      [X, Y] => (lInvertSub: One -⚬ (X |*| Y)) =>
        lInvertLPollableF(lInvertElem, lInvertSub >>> swap)
    )

  implicit def subscriberPollableDuality[A, B](implicit AB: Dual[A, B]): Dual[LSubscriber[B], LPollable[A]] =
    new Dual[LSubscriber[B], LPollable[A]] {
      val rInvert: (LSubscriber[B] |*| LPollable[A]) -⚬ One =
        rInvertLSubscriber(AB.rInvert)
      val lInvert: One -⚬ (LPollable[A] |*| LSubscriber[B]) =
        lInvertLPollable(AB.lInvert)
    }

  implicit def pollableSubscriberDuality[A, B](implicit BA: Dual[B, A]): Dual[LPollable[B], LSubscriber[A]] =
    dualSymmetric(subscriberPollableDuality[B, A])
}
