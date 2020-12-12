package libretto

object Streams {
  def apply[DSL <: ScalaDSL](dsl0: DSL)(lib0: CoreLib[dsl0.type]): Streams[DSL] =
    new Streams[DSL] {
      val dsl: dsl0.type = dsl0
      val lib = lib0
    }
}

sealed trait Streams[DSL <: ScalaDSL] {
  val dsl: DSL
  val lib: CoreLib[dsl.type]

  private val Tree: BinarySearchTree[dsl.type] =
    BinarySearchTree[dsl.type](dsl)(lib)

  import dsl._
  import lib._
  import Tree._

  type LPollableF[A, X] = Done |&| (Done |+| (A |*| X))
  type LPollable[A] = Rec[LPollableF[A, *]]
  type LPolled[A] = Done |+| (A |*| LPollable[A])

  type PollableF[A, X] = LPollableF[Val[A], X]
  type Pollable[A] = LPollable[Val[A]]
  type Polled[A] = LPolled[Val[A]]

  type LSubscriberF[A, X]  = Need |+| (Need |&| (A |*| X))
  type LSubscriber[A] = Rec[LSubscriberF[A, *]]
  type LDemanding[A] = Need |&| (A |*| LSubscriber[A])

  type SubscriberF[A, X]  = LSubscriberF[Neg[A], X]
  type Subscriber[A] = LSubscriber[Neg[A]]
  type Demanding[A] = LDemanding[Neg[A]]

  type ProducingF[A, X]  = Done |+| (Done |&| (Val[A] |*| X))
  type Producing[A] = Rec[ProducingF[A, *]]

  type ConsumerF[A, X] = Need |&| (Need |+| (Neg[A] |*| X))
  type Consumer[A] = Rec[ConsumerF[A, *]]

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
        .timesAssocLR                           .to[ Need |*| (Done |*| LPollable[A]) ]
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

  object Pollable {
    def close[A]: Pollable[A] -⚬ Done =
      LPollable.close[Val[A]]

    def poll[A]: Pollable[A] -⚬ Polled[A] =
      LPollable.poll[Val[A]]

    def delayedPoll[A]: (Done |*| Pollable[A]) -⚬ Polled[A] =
      LPollable.delayedPoll[Val[A]]

    /** Polls and discards all elements. */
    def drain[A]: Pollable[A] -⚬ Done =
      LPollable.drain[Val[A]]

    def emptyF[A]: Done -⚬ PollableF[A, Pollable[A]] =
      LPollable.emptyF[Val[A]]

    def empty[A]: Done -⚬ Pollable[A] =
      LPollable.empty[Val[A]]

    def delay[A]: Pollable[A] -⚬ Delayed[Pollable[A]] =
      LPollable.delay[Val[A]]

    def delayBy[A]: (Done |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.delayBy[Val[A]]

    def fromList[A]: Val[List[A]] -⚬ Pollable[A] = rec { self =>
      val uncons: List[A] => Option[(A, List[A])] = _ match {
        case a :: as => Some((a, as))
        case Nil => None
      }

      val close: Val[List[A]] -⚬ Done = neglect

      val poll: Val[List[A]] -⚬ Polled[A] =
        liftV(uncons)                           .to[      Val[Option[(A, List[A])]]     ]
          .andThen(PMaybe.liftOption)           .to[ Done |+|    Val[(A, List[A])]      ]
          .in.right(liftPair)                   .to[ Done |+| (Val[A] |*| Val[List[A]]) ]
          .in.right.snd(self)                   .to[ Done |+| (Val[A] |*| Pollable[A] ) ]

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    def map[A, B](f: A => B): Pollable[A] -⚬ Pollable[B] = {
      val g: Val[A] -⚬ Val[B] = liftV(f)
      LPollable.map(g)
    }

    def prepend[A]: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] = {
      val close: (Val[A] |*| Pollable[A]) -⚬ Done =
        join(neglect, Pollable.close)

      val poll: (Val[A] |*| Pollable[A]) -⚬ Polled[A] =
        injectR

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    def concat[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] =
      id                                       [ Pollable[A] |*|         Pollable[A]  ]
        .in.snd(delay)                      .to[ Pollable[A] |*| Delayed[Pollable[A]] ]
        .andThen(LPollable.concat)          .to[         Pollable[A]                  ]

    /** Splits a stream of "`A` or `B`" to a stream of `A` and a stream of `B`.
      *
      * Polls the upstream only after ''both'' downstreams poll.
      * When either of the downstreams closes, the other downstream and the upstream are closed as well.
      */
    def partition[A, B]: Pollable[Either[A, B]] -⚬ (Pollable[A] |*| Pollable[B]) =
      LPollable.map(liftEither[A, B]) >>> LPollable.partition

    /** Merges two [[Pollable]]s into one. When there is a value available from both upstreams, favors the first one. */
    def merge[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] = rec { self =>
      val close: (Pollable[A] |*| Pollable[A]) -⚬ Done =
        join(Pollable.close, Pollable.close)

      val unpoll: Polled[A] -⚬ Pollable[A] = {
        val closePolled: Polled[A] -⚬ Done =
          either(id, join(neglect, Pollable.close))

        choice(closePolled, id[Polled[A]])
          .pack[PollableF[A, *]]
      }

      // checks the first argument first, uses the given function for recursive calls
      def go(merge: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A]): (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        id[Polled[A] |*| Polled[A]]   .to[ (Done |+| (Val[A] |*| Pollable[A])) |*| Polled[A]                   ]
          .distributeRL               .to[ (Done |*| Polled[A]) |+| ((Val[A] |*| Pollable[A]) |*|  Polled[A] ) ]
          .in.left(Polled.delayBy[A]) .to[           Polled[A]  |+| ((Val[A] |*| Pollable[A]) |*|  Polled[A] ) ]
          .in.right.snd(unpoll)       .to[           Polled[A]  |+| ((Val[A] |*| Pollable[A]) |*| Pollable[A]) ]
          .in.right(timesAssocLR)     .to[           Polled[A]  |+| (Val[A] |*| (Pollable[A] |*| Pollable[A])) ]
          .in.right.snd(merge)        .to[           Polled[A]  |+| (Val[A] |*|          Pollable[A]         ) ]
          .in.right.injectR[Done]     .to[           Polled[A]  |+|       Polled[A]                            ]
          .andThen(either(id, id))    .to[                   Polled[A]                                         ]

      // checks the first argument first
      val goFst: (Polled[A] |*| Polled[A]) -⚬ Polled[A] = go(self)

      // checks the second argument first
      val goSnd: (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        swap[Polled[A], Polled[A]]
          .andThen(go(swap[Pollable[A], Pollable[A]] andThen self))

      val poll: (Pollable[A] |*| Pollable[A]) -⚬ Polled[A] = {
        import Polled.positivePolled

        id[Pollable[A] |*| Pollable[A]]               .to[ Pollable[A] |*| Pollable[A] ]
          .par(Pollable.poll[A], Pollable.poll[A])    .to[  Polled[A]  |*|  Polled[A]  ]
          .race(goFst, goSnd)                         .to[           Polled[A]         ]
      }

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    implicit def negativePollable[A]: SignalingJunction.Negative[Pollable[A]] =
      LPollable.negativeLPollable[Val[A]]

    def dup[A]: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) = rec { self =>
      val dupPolled: Polled[A] -⚬ (Polled[A] |*| Polled[A]) = {
        val caseClosed: Done -⚬ (Polled[A] |*| Polled[A]) =
          fork(injectL, injectL)

        val caseValue: (Val[A] |*| Pollable[A]) -⚬ (Polled[A] |*| Polled[A]) =
          id                                             [        Val[A]       |*|          Pollable[A]          ]
            .par(dsl.dup[A], self)                    .to[ (Val[A] |*| Val[A]) |*| (Pollable[A] |*| Pollable[A]) ]
            .andThen(IXI)                             .to[ (Val[A] |*| Pollable[A]) |*| (Val[A] |*| Pollable[A]) ]
            .in.fst.injectR[Done].in.snd.injectR[Done].to[       Polled[A]          |*|       Polled[A]          ]

        either(caseClosed, caseValue)
      }

      val caseFstClosed: Pollable[A] -⚬ (Done |*| Pollable[A]) =
        introFst >>> par(done, id)

      val caseFstPolled: Pollable[A] -⚬ (Polled[A] |*| Pollable[A]) =
        id                                           [                  Pollable[A]                       ]
          .andThen(Pollable.poll[A])              .to[                   Polled[A]                        ]
          .andThen(choice(introSnd, dupPolled))   .to[ (Polled[A] |*| One)  |&| (Polled[A] |*| Polled[A]) ]
          .andThen(coDistributeL)                 .to[  Polled[A] |*| (One  |&|                Polled[A]) ]
          .in.snd.choiceL(done)                   .to[  Polled[A] |*| (Done |&|                Polled[A]) ]
          .in.snd(pack[PollableF[A, *]])          .to[  Polled[A] |*|       Pollable[A]                   ]

      // the case when the first output polls or closes before the second output does
      val caseFst: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) =
        id                                           [                   Pollable[A]                           ]
          .choice(caseFstClosed, caseFstPolled)   .to[ (Done |*| Pollable[A]) |&| (Polled[A]  |*| Pollable[A]) ]
          .andThen(coDistributeR)                 .to[ (Done                  |&|  Polled[A]) |*| Pollable[A]  ]
          .in.fst(pack[PollableF[A, *]])          .to[              Pollable[A]               |*| Pollable[A]  ]

      // the case when the second output polls or closes before the first output does
      val caseSnd: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) =
        caseFst andThen swap

      id                                   [          Pollable[A]        ]
        .select(caseFst, caseSnd)       .to[ Pollable[A] |*| Pollable[A] ]
    }

    def dropUntilFirstDemand[A]: Pollable[A] -⚬ Pollable[A] = {
      val goUnpacked: (Done |&| Polled[A]) -⚬ (Done |&| Polled[A]) = rec { self =>
        val caseDownstreamRequested: (Val[A] |*| Pollable[A]) -⚬ (Done |&| Polled[A]) = {
          val caseDownstreamClosed: (Val[A] |*| Pollable[A]) -⚬ Done      = join(neglect, Pollable.close)
          val caseDownstreamPulled: (Val[A] |*| Pollable[A]) -⚬ Polled[A] = injectR
          choice(caseDownstreamClosed, caseDownstreamPulled)
        }

        val caseNotRequestedYet: (Val[A] |*| Pollable[A]) -⚬ (Done |&| Polled[A]) = {
          id[Val[A] |*| Pollable[A]]
            .in.fst(neglect)
            .andThen(Pollable.delayBy)
            .unpack
            .andThen(self)
        }

        val goElem: (Val[A] |*| Pollable[A]) -⚬ (Done |&| Polled[A]) =
          choice(caseDownstreamRequested, caseNotRequestedYet)
            .andThen(selectSignaledOrNot(LPollable.negativeLPollableF))

        id                               [ Done |&| Polled[A]                ]
          .chooseR                    .to[ Done |+| (Val[A] |*| Pollable[A]) ]
          .either(emptyF[A], goElem)  .to[ Done |&| Polled[A]                ]
      }

      unpack[PollableF[A, *]]
        .andThen(goUnpacked)
        .pack[PollableF[A, *]]
    }

    def broadcast[A]: Pollable[A] -⚬ PUnlimited[Pollable[A]] = rec { self =>
      val case0: Pollable[A] -⚬ Done                                                  = Pollable.close
      val case1: Pollable[A] -⚬ Pollable[A]                                           = id
      val caseN: Pollable[A] -⚬ (PUnlimited[Pollable[A]] |*| PUnlimited[Pollable[A]]) = dup andThen par(self, self)

      dropUntilFirstDemand
        .choice(case0, (choice(case1, caseN)))
        .pack[PUnlimitedF[Pollable[A], *]]
    }

    private[Pollable] type DemandingTree[K, V] = Tree[K, Demanding[V]]
    private[Pollable] object DemandingTree {
      type DT[K, V] = DemandingTree[K, V]
      type NeDT[K, V] = NonEmptyTree[K, Demanding[V]]

      def dispatch[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| DT[K, V]) -⚬ (Done |*| DT[K, V]) =
        Tree.update(Demanding.supply[V].in.left(need >>> done))
          .in.fst(PMaybe.neglect)

      def dispatchNE[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        NonEmptyTree.update(
          Demanding.supply[V].in.left(need >>> done),
          ifAbsent = neglect,
        )

      def dispatchNE[A, K: Ordering, V](
        f: Val[A] -⚬ (Val[K] |*| Val[V]),
      ): (Val[A] |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        id                                     [       Val[A]        |*| NeDT[K, V]  ]
          .in.fst(f)                        .to[ (Val[K] |*| Val[V]) |*| NeDT[K, V]  ]
          .andThen(dispatchNE)              .to[                  PMaybe[NeDT[K, V]] ]

      def addDemanding[K: Ordering, V]: ((Val[K] |*| Demanding[V]) |*| DT[K, V]) -⚬ DT[K, V] =
        Tree.insertOrUpdate(Demanding.merge)

      def clear[K, V]: DT[K, V] -⚬ Done =
        Tree.clear(Demanding.close >>> need >>> done)

      def clearNE[K, V]: NeDT[K, V] -⚬ Done =
        NonEmptyTree.clear(Demanding.close >>> need >>> done)

      def addSubscriber[K: Ordering, V]: ((Val[K] |*| Subscriber[V]) |*| DT[K, V]) -⚬ DT[K, V] =
        id                                           [ ( Val[K] |*|       Subscriber[V]                ) |*| DT[K, V] ]
          .in.fst.snd(unpack)                     .to[ ( Val[K] |*| (Need |+|             Demanding[V])) |*| DT[K, V] ]
          .in.fst(distributeLR)                   .to[ ((Val[K] |*| Need) |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .in.fst.left.fst(neglect)               .to[ (( Done  |*| Need) |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .in.fst.left(rInvertSignal)             .to[ (        One       |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .distributeRL
          .either(elimFst, addDemanding)
    }

    def subscribeByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): (Pollable[A] |*| LPollable[Val[K] |*| Subscriber[V]]) -⚬ Done = {
      import Pollable.{DemandingTree => DT}
      import DemandingTree.NeDT
      type KSubs = Val[K] |*| Subscriber[V]

      val discardSubscriber: KSubs -⚬ One =
        par(dsl.neglect[K], Subscriber.close[V]) >>> rInvertSignal

      val upstreamClosed: (Done |*| (LPolled[KSubs] |*| DT[K, V])) -⚬ Done =
        join(id, join(LPolled.close(discardSubscriber >>> done), DT.clear))

      def upstreamVal(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Val[A] |*| Pollable[A]) |*| (LPolled[KSubs] |*| DT[K, V])) -⚬ Done =
        id                                   [ (Val[A] |*| Pollable[A]) |*|              (LPolled[KSubs] |*| DT[K, V]) ]
          .in.fst(swap)                   .to[ (Pollable[A] |*| Val[A]) |*|              (LPolled[KSubs] |*| DT[K, V]) ]
          .andThen(IXI)                   .to[ (Pollable[A] |*| LPolled[KSubs]) |*| (      Val[A]        |*| DT[K, V]) ]
          .in.snd.fst(f)                  .to[ (Pollable[A] |*| LPolled[KSubs]) |*| ((Val[K] |*| Val[V]) |*| DT[K, V]) ]
          .in.snd(DT.dispatch)            .to[ (Pollable[A] |*| LPolled[KSubs]) |*| (Done                |*| DT[K, V]) ]
          .timesAssocRL                   .to[ ((Pollable[A] |*| LPolled[KSubs]) |*| Done)               |*| DT[K, V]  ]
          .in.fst(swap >>> timesAssocRL)  .to[ ((Done |*| Pollable[A]) |*| LPolled[KSubs])               |*| DT[K, V]  ]
          .in.fst.fst(delayedPoll)        .to[ (  Polled[A]            |*| LPolled[KSubs])               |*| DT[K, V]  ]
          .andThen(goRec)                 .to[                                                          Done           ]

      def onUpstream(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done =
        timesAssocLR      .to[ Polled[A] |*| (LPolled[KSubs] |*| DT[K, V]) ]
          .distributeRL
          .either(upstreamClosed, upstreamVal(goRec))

      val feedToNEDT: (Polled[A] |*| NeDT[K, V]) -⚬ Done =
        LPolled.feedTo(DT.dispatchNE(f)) >>> join(id, Maybe.neglect(DT.clearNE))

      val forward: (Polled[A] |*| DT[K, V]) -⚬ Done =
        id                                               [  Polled[A] |*| (Done |+|                NeDT[K, V]) ]
          .distributeLR                               .to[ (Polled[A] |*| Done) |+| (Polled[A] |*| NeDT[K, V]) ]
          .in.left(join(Polled.close, id))            .to[           Done       |+| (Polled[A] |*| NeDT[K, V]) ]
          .in.right(feedToNEDT)                       .to[           Done       |+|           Done             ]
          .andThen(either(id, id))                    .to[                     Done                            ]

      val subsClosed: ((Polled[A] |*| Done) |*| DT[K, V]) -⚬ Done =
        id                             [ (Polled[A] |*| Done) |*| DT[K, V] ]
          .andThen(IX)              .to[ (Polled[A] |*| DT[K, V]) |*| Done ]
          .in.fst(forward)          .to[           Done           |*| Done ]
          .andThen(join)            .to[                         Done      ]

      def newSubscriber(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| (KSubs |*| LPollable[KSubs])) |*| DT[K, V]) -⚬ Done =
        id                               [ ( Polled[A] |*| (KSubs  |*|  LPollable[KSubs])) |*| DT[K, V]  ]
        .in.fst.snd(swap)             .to[ ( Polled[A] |*| (LPollable[KSubs]  |*|  KSubs)) |*| DT[K, V]  ]
        .in.fst(timesAssocRL)         .to[ ((Polled[A] |*|  LPollable[KSubs]) |*|  KSubs ) |*| DT[K, V]  ]
        .timesAssocLR                 .to[  (Polled[A] |*|  LPollable[KSubs]) |*| (KSubs   |*| DT[K, V]) ]
        .in.snd(DT.addSubscriber)     .to[  (Polled[A] |*|  LPollable[KSubs]) |*|              DT[K, V]  ]
        .in.fst.snd(LPollable.poll)   .to[  (Polled[A] |*|    LPolled[KSubs]) |*|              DT[K, V]  ]
        .andThen(goRec)               .to[                                   Done                        ]

      def onSubs(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done =
        id[ (Polled[A] |*| LPolled[KSubs]) |*| DT[K, V] ]
          .in.fst(distributeLR)
          .distributeRL
          .either(subsClosed, newSubscriber(goRec))

      val go: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done = rec { self =>
        import LPolled.positiveLPolled

        implicit def positiveKSubs: SignalingJunction.Positive[KSubs] =
          SignalingJunction.Positive.byFst[Val[K], Subscriber[V]]

        id                                           [ (Polled[A] |*| LPolled[KSubs]) |*| DT[K, V] ]
          .in.fst(lib.race)
          .distributeRL
          .either(onUpstream(self), onSubs(self)) .to[                               Done          ]
      }

      id[Pollable[A] |*| LPollable[KSubs]]
        .andThen(par(poll, LPollable.poll))
        .introSnd(done >>> Tree.empty[K, Demanding[V]])
        .andThen(go)
    }
  }

  object LPolled {
    def close[A](neglect: A -⚬ Done): LPolled[A] -⚬ Done =
      either(id, join(neglect, LPollable.close))

    def empty[A]: Done -⚬ LPolled[A] =
      injectL

    def cons[A]: (A |*| LPollable[A]) -⚬ LPolled[A] =
      injectR

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
          .timesAssocLR                             .to[  LPollable[A] |*| (    A        |*|           B) ]
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
  }

  object Polled {
    def close[A]: Polled[A] -⚬ Done =
      LPolled.close(dsl.neglect[A])

    def empty[A]: Done -⚬ Polled[A] =
      LPolled.empty

    def cons[A]: (Val[A] |*| Pollable[A]) -⚬ Polled[A] =
      LPolled.cons

    def delayBy[A]: (Done |*| Polled[A]) -⚬ Polled[A] =
      LPolled.delayBy

    implicit def positivePolled[A]: SignalingJunction.Positive[Polled[A]] =
      LPolled.positiveLPolled[Val[A]]
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

  object Subscriber {
    implicit def positiveSubscriber[A]: SignalingJunction.Positive[Subscriber[A]] =
      LSubscriber.positiveLSubscriber[Neg[A]]

    def close[A]: Subscriber[A] -⚬ Need =
      LSubscriber.close

    private[Streams] def merge[A](
      mergeDemandings: (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A]
    ): (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] = {
      val fstClosed: (Need |*| Subscriber[A]) -⚬ Subscriber[A] =
        elimFst(need)

      val fstDemanding: (Demanding[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        id                                                     [  Demanding[A] |*|       Subscriber[A]                       ]
          .in.snd(unpack)                                   .to[  Demanding[A] |*| (Need |+|                   Demanding[A]) ]
          .distributeLR                                     .to[ (Demanding[A] |*| Need) |+| (Demanding[A] |*| Demanding[A]) ]
          .andThen(either(elimSnd(need), mergeDemandings))  .to[                     Demanding[A]                            ]
          .injectR[Need].pack[SubscriberF[A, *]]            .to[                    Subscriber[A]                            ]

      val caseFstReady: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        id                                     [       Subscriber[A]                         |*| Subscriber[A]  ]
          .in.fst(unpack)                   .to[ (Need |+|                     Demanding[A]) |*| Subscriber[A]  ]
          .distributeRL                     .to[ (Need |*| Subscriber[A]) |+| (Demanding[A]  |*| Subscriber[A]) ]
          .either(fstClosed, fstDemanding)  .to[                     Subscriber[A]                              ]

      val caseSndReady: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        swap >>> caseFstReady

      id                                         [ Subscriber[A] |*| Subscriber[A] ]
        .race(caseFstReady, caseSndReady)     .to[           Subscriber[A]         ]
    }

    def merge[A]: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] = rec { self =>
      merge(Demanding.merge(self))
    }
  }

  object LDemanding {
    def supply[A, B](rInvert: (A |*| B) -⚬ One): (A |*| LDemanding[B]) -⚬ (Need |+| LDemanding[B]) =
      id[ A |*| LDemanding[B] ]     .to[ A |*| (Need |&| (B |*| LSubscriber[B])) ]
      .in.snd(chooseR)              .to[ A |*|           (B |*| LSubscriber[B])  ]
      .timesAssocRL                 .to[ (A |*| B)          |*| LSubscriber[B]   ]
      .elimFst(rInvert)             .to[                        LSubscriber[B]   ]
      .unpack[LSubscriberF[B, *]]   .to[                  Need |+| LDemanding[B] ]

    implicit def negativeLDemanding[A](implicit A: Junction.Negative[A]): SignalingJunction.Negative[LDemanding[A]] =
      SignalingJunction.Negative.choiceNeg(
        SignalingJunction.Negative.signalingJunctionNegativeNeed,
        Junction.Negative.byFst(A),
      )
  }

  object Demanding {
    def close[A]: Demanding[A] -⚬ Need =
      chooseL

    def supply[A]: (Val[A] |*| Demanding[A]) -⚬ (Need |+| Demanding[A]) =
      LDemanding.supply(fulfill[A])

    private[Streams] def merge[A](
      mergeSubscribers: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A]
    ): (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A] = {
      val caseClosed: (Demanding[A] |*| Demanding[A]) -⚬ Need =
        forkNeed(chooseL, chooseL)

      val caseDemanding: (Demanding[A] |*| Demanding[A]) -⚬ (Neg[A] |*| Subscriber[A]) =
        id                                             [     Demanding[A]           |*|     Demanding[A]           ]
          .andThen(par(chooseR, chooseR))           .to[ (Neg[A] |*| Subscriber[A]) |*| (Neg[A] |*| Subscriber[A]) ]
          .andThen(IXI)                             .to[ (Neg[A] |*| Neg[A]) |*| (Subscriber[A] |*| Subscriber[A]) ]
          .par(mergeDemands[A], mergeSubscribers)   .to[        Neg[A]       |*|            Subscriber[A]          ]

      choice(caseClosed, caseDemanding)
    }

    def merge[A]: (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A] = rec { self =>
      merge(Subscriber.merge(self))
    }

    implicit def negativeDemanding[A]: SignalingJunction.Negative[Demanding[A]] =
      LDemanding.negativeLDemanding[Neg[A]]
  }

  def rInvertProducingF[A, x, y](rInvertSub: (x |*| y) -⚬ One): (ProducingF[A, x] |*| ConsumerF[A, y]) -⚬ One =
    rInvertEither(
      rInvertSignal,
      swap >>> rInvertEither(
        swap >>> rInvertSignal,
        rInvertTimes(
          swap >>> fulfill[A],
          swap >>> rInvertSub
        )
      )
    )

  def lInvertConsumerF[A, x, y](lInvertSub: One -⚬ (y |*| x)): One -⚬ (ConsumerF[A, y] |*| ProducingF[A, x]) =
    lInvertChoice(
      lInvertSignal,
      lInvertChoice(
        lInvertSignal >>> swap,
        lInvertTimes(
          promise[A] >>> swap,
          lInvertSub >>> swap
        )
      ) >>> swap
    )

  implicit def producingConsumerDuality[A]: Dual[Producing[A], Consumer[A]] =
    dualRec[ProducingF[A, *], ConsumerF[A, *]](
      new Dual1[ProducingF[A, *], ConsumerF[A, *]] {
        def rInvert[x, y](rInvertSub: (x |*| y) -⚬ One): (ProducingF[A, x] |*| ConsumerF[A, y]) -⚬ One =
          rInvertProducingF(rInvertSub)
        def lInvert[x, y](lInvertSub: One -⚬ (y |*| x)): One -⚬ (ConsumerF[A, y] |*| ProducingF[A, x]) =
          lInvertConsumerF(lInvertSub)
      }
    )

  implicit def consumerProducingDuality[A]: Dual[Consumer[A], Producing[A]] =
    dualSymmetric(producingConsumerDuality[A])

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

  implicit def subscriberPollableDuality[A, B](implicit AB: Dual[A, B]): Dual[LSubscriber[B], LPollable[A]] =
    dualRec[LSubscriberF[B, *], LPollableF[A, *]](
      new Dual1[LSubscriberF[B, *], LPollableF[A, *]] {
        def rInvert[x, y](rInvertSub: (x |*| y) -⚬ One): (LSubscriberF[B, x] |*| LPollableF[A, y]) -⚬ One =
          rInvertLSubscriberF(AB.rInvert, swap >>> rInvertSub)
        def lInvert[x, y](lInvertSub: One -⚬ (y |*| x)): One -⚬ (LPollableF[A, y] |*| LSubscriberF[B, x]) =
          lInvertLPollableF  (AB.lInvert, lInvertSub >>> swap)
      }
    )

  implicit def pollableSubscriberDuality[A, B](implicit BA: Dual[B, A]): Dual[LPollable[B], LSubscriber[A]] =
    dualSymmetric(subscriberPollableDuality[B, A])

  /** If either the source or the subscriber is completed, complete the other one and be done.
    * Otherwise, expose their offer and demand, respectively.
    */
  def relayCompletion[A, B]: (Pollable[A] |*| Subscriber[B]) -⚬ (One |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B]))) =
    id                                [ Pollable[A] |*| (                   Subscriber[B]                                     )]
      .in.snd(unpack)              .to[ Pollable[A] |*| (Need   |+|                      (Need |&| (Neg[B] |*| Subscriber[B])))]
      .distributeLR                .to[(Pollable[A] |*|  Need)  |+|   (Pollable[A]   |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .in.left.fst(Pollable.close) .to[(Done        |*|  Need)  |+|   (Pollable[A]   |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .in.left(rInvertSignal)      .to[ One |+| (                      Pollable[A]   |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .in.right.fst(Pollable.poll) .to[ One |+| ((Done |+| (Val[A] |*| Pollable[A])) |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .in.right(matchingChoiceLR)  .to[ One |+| ((Done |*| Need) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])))]
      .in.right.left(rInvertSignal).to[ One |+| (      One       |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])))]
      .plusAssocRL                 .to[(One |+|        One     ) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]
      .in.left(either(id, id))     .to[     One                  |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]

  type Pipe[A, B] = Pollable[A] -⚬ Pollable[B]
  object Pipe {
    def lift[A, B](f: A => B): Pipe[A, B] = {
      val ff: Val[A] -⚬ Val[B] = liftV(f)

      rec(self =>
        id[Pollable[A]]                     .to[    Pollable[A]                               ]
          .unpack                           .to[ Done |&| (Done |+| (Val[A] |*| Pollable[A])) ]
          .in.choiceR.right.fst(ff)         .to[ Done |&| (Done |+| (Val[B] |*| Pollable[A])) ]
          .in.choiceR.right.snd(self)       .to[ Done |&| (Done |+| (Val[B] |*| Pollable[B])) ]
          .pack[PollableF[B, *]]            .to[                                Pollable[B]   ]
      )
    }

    def statefulMap[S, A, B](f: ((S, A)) => (S, B))(initialState: S): Pipe[A, B] = {
      val ff: (Val[S] |*| Val[A]) -⚬ (Val[S] |*| Val[B]) =
        unliftPair[S, A]
          .andThen(liftV(f))
          .andThen(liftPair[S, B])

      val inner: (Val[S] |*| Pollable[A]) -⚬ Pollable[B] = rec { self =>
        val close: (Val[S] |*| Pollable[A]) -⚬ Done =
          join(neglect, Pollable.close)

        val poll:(Val[S] |*| Pollable[A]) -⚬ (Done |+| (Val[B] |*| Pollable[B])) =
          id[Val[S] |*| Pollable[A]]          .to[ Val[S] |*|                                    Pollable[A]   ]
            .in.snd(Pollable.poll)            .to[ Val[S] |*| (Done  |+|             (Val[A] |*| Pollable[A])) ]
            .distributeLR                     .to[ (Val[S] |*| Done) |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .in.left(join(neglect, id))       .to[        Done       |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .in.right(timesAssocRL)           .to[        Done       |+| ((Val[S] |*| Val[A]) |*| Pollable[A]) ]
            .in.right.fst(ff)                 .to[        Done       |+| ((Val[S] |*| Val[B]) |*| Pollable[A]) ]
            .in.right.fst(swap)               .to[        Done       |+| ((Val[B] |*| Val[S]) |*| Pollable[A]) ]
            .in.right(timesAssocLR)           .to[        Done       |+| (Val[B] |*| (Val[S] |*| Pollable[A])) ]
            .in.right.snd(self)               .to[        Done       |+| (Val[B] |*|     Pollable[B]         ) ]

        choice(close, poll)
          .pack[PollableF[B, *]]
      }

      id[Pollable[A]]                   .to[            Pollable[A] ]
        .introFst(const_(initialState)) .to[ Val[S] |*| Pollable[A] ]
        .andThen(inner)                 .to[     Pollable[B]        ]
    }
  }
}
