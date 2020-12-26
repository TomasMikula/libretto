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
        .in.snd(unpack)                     .to[ Done |*| (Done |&| LPolled[A]) ]
        .andThen(chooseRWhenDone)           .to[ Done |*|           LPolled[A]  ]
        .andThen(LPolled.delayBy[A])        .to[                    LPolled[A]  ]

    /** Polls and discards all elements. */
    def drain[A](implicit A: PComonoid[A]): LPollable[A] -⚬ Done =
      rec { self =>
        poll[A] andThen either(id, join(A.counit, self))
      }

    def emptyF[A]: Done -⚬ LPollableF[A, LPollable[A]] =
      choice[Done, Done, LPolled[A]](id, injectL)

    def empty[A]: Done -⚬ LPollable[A] =
      emptyF[A].pack
      
    def cons[A](implicit A: PComonoid[A]): (A |*| LPollable[A]) -⚬ LPollable[A] = {
      val onClose: (A |*| LPollable[A]) -⚬ Done       = join(A.counit, LPollable.close)
      val onPoll:  (A |*| LPollable[A]) -⚬ LPolled[A] = LPolled.cons
      choice(onClose, onPoll).pack
    }
    
    def fromLList[A](implicit A: PComonoid[A]): LList[A] -⚬ LPollable[A] = rec { self =>
      LList.switch(
        caseNil  = done          >>> LPollable.empty[A],
        caseCons = par(id, self) >>> LPollable.cons[A],
      )
    }
    
    def of[A](as: (One -⚬ A)*)(implicit A: PComonoid[A]): One -⚬ LPollable[A] =
      LList.of(as: _*) >>> fromLList

    def delayBy[A](implicit ev: Junction.Positive[A]): (Done |*| LPollable[A]) -⚬ LPollable[A] =
      id                                           [  Done |*|     LPollable[A]                 ]
        .in.snd(unpack)                         .to[  Done |*| (Done  |&|           LPolled[A]) ]
        .andThen(delayChoiceUntilDone)          .to[  Done |*| (Done  |&|           LPolled[A]) ]
        .coFactorL                              .to[ (Done |*| Done)  |&| (Done |*| LPolled[A]) ]
        .bimap(join, LPolled.delayBy[A])        .to[      Done        |&|           LPolled[A]  ]
        .pack[LPollableF[A, *]]                 .to[              LPollable[A]                  ]

    def delay[A: Junction.Positive]: LPollable[A] -⚬ Delayed[LPollable[A]] =
      id                                           [                     LPollable[A] ]
        .introFst(lInvertSignal)                .to[ (Need |*| Done) |*| LPollable[A] ]
        .assocLR                                .to[ Need |*| (Done |*| LPollable[A]) ]
        .in.snd(delayBy)                        .to[ Need |*|     LPollable[A]        ]

    def map[A, B](f: A -⚬ B): LPollable[A] -⚬ LPollable[B] = rec { self =>
      choice(close[A], poll[A].in.right(par(f, self))).pack
    }

    def concat[A]: (LPollable[A] |*| Delayed[LPollable[A]]) -⚬ LPollable[A] = rec { self =>
      val close: (LPollable[A] |*| Delayed[LPollable[A]]) -⚬ Done =
        join(LPollable.close, Delayed.force >>> LPollable.close)

      val poll: (LPollable[A] |*| Delayed[LPollable[A]]) -⚬ LPolled[A] =
        id                               [                                               LPollable[A]    |*| Delayed[LPollable[A]]   ]
          .in.fst(unpack)             .to[ (Done |&| (Done                  |+|  (A |*|  LPollable[A]))) |*| Delayed[LPollable[A]]   ]
          .in.fst(chooseR)            .to[           (Done                  |+|  (A |*|  LPollable[A]))  |*| Delayed[LPollable[A]]   ]
          .distributeRL               .to[ (Done |*| Delayed[LPollable[A]]) |+| ((A |*|  LPollable[A])   |*| Delayed[LPollable[A]] ) ]
          .in.left(Delayed.triggerBy) .to[                   LPollable[A]   |+| ((A |*|  LPollable[A])   |*| Delayed[LPollable[A]] ) ]
          .in.left(LPollable.poll)    .to[                     LPolled[A]   |+| ((A |*|  LPollable[A])   |*| Delayed[LPollable[A]] ) ]
          .in.right(timesAssocLR)     .to[                     LPolled[A]   |+| ( A |*| (LPollable[A]    |*| Delayed[LPollable[A]])) ]
          .in.right.snd(self)         .to[                     LPolled[A]   |+| ( A |*|            LPollable[A]                    ) ]
          .in.right.injectR[Done]     .to[                     LPolled[A]   |+|     LPolled[A]                                       ]
          .andThen(either(id, id))    .to[                              LPolled[A]                                                   ]

      choice(close, poll)
        .pack[LPollableF[A, *]]
    }

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
            .in.snd(self)                 .to[ (A                                      |+|  B) |*| (LPollable[A] |*| LPollable[B])  ]
            .distributeRL                 .to[ (A |*| (LPollable[A] |*| LPollable[B])) |+| (B  |*| (LPollable[A] |*| LPollable[B])) ]
            .in.left(timesAssocRL)        .to[ ((A |*| LPollable[A]) |*| LPollable[B]) |+| (B  |*| (LPollable[A] |*| LPollable[B])) ]
            .in.right(XI)                 .to[ ((A |*| LPollable[A]) |*| LPollable[B]) |+| (LPollable[A] |*|  (B |*| LPollable[B])) ]
            .in .left.fst(LPolled.cons)   .to[ (  LPolled[A]         |*| LPollable[B]) |+| (LPollable[A] |*|  (B |*| LPollable[B])) ]
            .in.right.snd(LPolled.cons)   .to[ (  LPolled[A]         |*| LPollable[B]) |+| (LPollable[A] |*|    LPolled[B]        ) ]
            .in .left.snd(poll)           .to[ (  LPolled[A]         |*|   LPolled[B]) |+| (LPollable[A] |*|    LPolled[B]        ) ]
            .in.right.fst(poll)           .to[ (  LPolled[A]         |*|   LPolled[B]) |+| (  LPolled[A] |*|    LPolled[B]        ) ]
            .either(id, id)

        id                                   [   LPollable[A |+| B]                        ]
          .andThen(poll)                  .to[ Done |+| ((A |+| B) |*| LPollable[A |+| B]) ]
          .either(upClosed, upValue)      .to[         LPolled[A] |*| LPolled[B]           ]
      }

      val fstPolled: LPollable[A |+| B] -⚬ (LPolled[A] |*| LPollable[B]) =
        id                                   [                 LPollable[A |+| B]                    ]
          .choice(sndClosed, bothPolled)  .to[ (LPolled[A] |*| Done) |&| (LPolled[A] |*| LPolled[B]) ]
          .coDistributeL                  .to[  LPolled[A] |*| (Done |&|                 LPolled[B]) ]
          .in.snd(pack)                   .to[  LPolled[A] |*|   LPollable[B]                        ]

      id                                 [                   LPollable[A |+| B]                      ]
        .choice(fstClosed, fstPolled) .to[ (Done |*| LPollable[B]) |&| (LPolled[A] |*| LPollable[B]) ]
        .coDistributeR                .to[ (Done                   |&| LPolled[A]) |*| LPollable[B]  ]
        .in.fst(pack)                 .to[                     LPollable[A]        |*| LPollable[B]  ]
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
      choice(onClose, onPoll).pack
    }

    implicit def negativeLPollableF[A, X](implicit A: Junction.Positive[A]): SignalingJunction.Negative[LPollableF[A, X]] =
      SignalingJunction.Negative.choicePos(
        Junction.Positive.junctionDone,
        Junction.Positive.eitherInstance(
          Junction.Positive.junctionDone,
          Junction.Positive.byFst(A),
        ),
      )

    implicit def universalNegativeLPollableF[A](implicit A: Junction.Positive[A]): ∀[λ[x => SignalingJunction.Negative[LPollableF[A, x]]]] =
      new ∀[λ[x => SignalingJunction.Negative[LPollableF[A, x]]]] {
        def apply[X]: SignalingJunction.Negative[LPollableF[A, X]] =
          negativeLPollableF[A, X]
      }

    implicit def negativeLPollable[A](implicit A: Junction.Positive[A]): SignalingJunction.Negative[LPollable[A]] =
      SignalingJunction.Negative.rec[LPollableF[A, *]](universalNegativeLPollableF[A])
  }

  object LPolled {
    def close[A](neglect: A -⚬ Done): LPolled[A] -⚬ Done =
      either(id, join(neglect, LPollable.close))

    def empty[A]: Done -⚬ LPolled[A] =
      injectL

    def cons[A]: (A |*| LPollable[A]) -⚬ LPolled[A] =
      injectR

    def unpoll[A](implicit A: PComonoid[A]): LPolled[A] -⚬ LPollable[A] =
      choice(close(A.counit), id).pack

    def delayBy[A](implicit ev: Junction.Positive[A]): (Done |*| LPolled[A]) -⚬ LPolled[A] =
      id[Done |*| LPolled[A]]         .to[  Done |*| (Done |+|           (A |*| LPollable[A])) ]
        .distributeLR                 .to[ (Done |*| Done) |+| (Done |*| (A |*| LPollable[A])) ]
        .in.left(join)                .to[      Done       |+| (Done |*| (A |*| LPollable[A])) ]
        .in.right(timesAssocRL)       .to[      Done       |+| ((Done |*| A) |*| LPollable[A]) ]
        .in.right.fst(ev.awaitPosFst) .to[      Done       |+| (          A  |*| LPollable[A]) ]

    def feedTo[A, B](
      f: (A |*| B) -⚬ PMaybe[B],
    ): (LPolled[A] |*| B) -⚬ (Done |*| Maybe[B]) = rec { self =>
      val upstreamValue: ((A |*| LPollable[A]) |*| B) -⚬ (Done |*| Maybe[B]) =
        id                                             [ (     A       |*| LPollable[A]) |*|           B  ]
          .in.fst(swap)                             .to[ (LPollable[A] |*|      A      ) |*|           B  ]
          .assocLR                                  .to[  LPollable[A] |*| (    A        |*|           B) ]
          .in.snd(f)                                .to[  LPollable[A] |*| (Done |+|                   B) ]
          .distributeLR                             .to[ (LPollable[A] |*| Done) |+| (LPollable[A] |*| B) ]
          .in.left(join(LPollable.close, id))       .to[              Done       |+| (LPollable[A] |*| B) ]
          .in.left(introSnd(Maybe.empty[B]))        .to[   (Done |*| Maybe[B])   |+| (LPollable[A] |*| B) ]
          .in.right.fst(LPollable.poll)             .to[   (Done |*| Maybe[B])   |+| (  LPolled[A] |*| B) ]
          .in.right(self)                           .to[   (Done |*| Maybe[B])   |+| ( Done |*| Maybe[B]) ]
          .andThen(either(id, id))                  .to[                 (Done |*| Maybe[B])              ]

      val upstreamClosed: (Done |*| B) -⚬ (Done |*| Maybe[B]) =
        par(id, Maybe.just)

      id[ (Done |+| (A |*| LPollable[A])) |*| B ]
        .distributeRL
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
          .distributeRL               .to[ (Done |*| LPolled[A]) |+| ((A |*| LPollable[A])  |*| LPolled[A]   ) ]
          .in.left(delayBy[A])        .to[           LPolled[A]  |+| ((A |*| LPollable[A])  |*| LPolled[A]   ) ]
          .in.right.snd(unpoll)       .to[           LPolled[A]  |+| ((A |*| LPollable[A])  |*| LPollable[A] ) ]
          .in.right.assocLR           .to[           LPolled[A]  |+| ( A |*| (LPollable[A]  |*| LPollable[A])) ]
          .in.right.snd(merge)        .to[           LPolled[A]  |+| ( A |*|           LPollable[A]          ) ]
          .in.right(cons)             .to[           LPolled[A]  |+|     LPolled[A]                            ]
          .andThen(either(id, id))    .to[                   LPolled[A]                                        ]

      // checks the first argument first
      val goFst: (LPolled[A] |*| LPolled[A]) -⚬ LPolled[A] = go(mergePollables)

      // checks the second argument first
      val goSnd: (LPolled[A] |*| LPolled[A]) -⚬ LPolled[A] =
        swap >>> go(swap >>> mergePollables)

      race(goFst, goSnd)
    }
  }

  object LSubscriber {
    def close[A]: LSubscriber[A] -⚬ Need =
      unpack[LSubscriberF[A, *]] >>> either(id, chooseL)

    implicit def positiveLSubscriberF[A, X](implicit A: Junction.Negative[A]): SignalingJunction.Positive[LSubscriberF[A, X]] =
      SignalingJunction.Positive.eitherNeg(
        Junction.Negative.junctionNeed,
        Junction.Negative.choiceInstance(
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
  }

  object LDemanding {
    def supply[A, B](rInvert: (A |*| B) -⚬ One): (A |*| LDemanding[B]) -⚬ (Need |+| LDemanding[B]) =
      id[ A |*| LDemanding[B] ]     .to[ A |*| (Need |&| (B |*| LSubscriber[B])) ]
      .in.snd(chooseR)              .to[ A |*|           (B |*| LSubscriber[B])  ]
      .assocRL                      .to[ (A |*| B)          |*| LSubscriber[B]   ]
      .elimFst(rInvert)             .to[                        LSubscriber[B]   ]
      .unpack[LSubscriberF[B, *]]   .to[                  Need |+| LDemanding[B] ]

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
      new ForAll2[[x, y] =>> ((x |*| y) -⚬ One) => ((LSubscriberF[B, x] |*| LPollableF[A, y]) -⚬ One)] {
        override def apply[X, Y] =
          rInvertSub => rInvertLSubscriberF(rInvertElem, swap >>> rInvertSub)
      },
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
      new ForAll2[[x, y] =>> (One -⚬ (x |*| y)) => (One -⚬ (LPollableF[A, x] |*| LSubscriberF[B, y]))] {
        override def apply[X, Y] =
          lInvertSub => lInvertLPollableF(lInvertElem, lInvertSub >>> swap)
      },
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
