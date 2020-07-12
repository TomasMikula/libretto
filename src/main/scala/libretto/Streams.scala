package libretto

object Streams {
  def apply[DSL <: libretto.DSL](dsl0: DSL)(lib0: Lib[dsl0.type]): Streams[DSL] =
    new Streams[DSL] {
      val dsl: dsl0.type = dsl0
      val lib = lib0
    }
}

sealed trait Streams[DSL <: libretto.DSL] {
  val dsl: DSL
  val lib: Lib[dsl.type]

  import dsl._
  import lib._

  type LPollableF[A, X] = One |&| (One |+| (A |*| X))
  type LPollable[A] = Rec[LPollableF[A, *]]
  type LPolled[A] = One |+| (A |*| LPollable[A])

  type PollableF[A, X] = LPollableF[Val[A], X]
  type Pollable[A] = LPollable[Val[A]]
  type Polled[A] = LPolled[Val[A]]

  type LSubscriberF[A, X]  = One |+| (One |&| (A |*| X))
  type LSubscriber[A] = Rec[LSubscriberF[A, *]]

  type SubscriberF[A, X]  = LSubscriberF[Neg[A], X]
  type Subscriber[A] = LSubscriber[Neg[A]]

  type ProducingF[A, X]  = One |+| (One |&| (Val[A] |*| X))
  type Producing[A] = Rec[ProducingF[A, *]]

  type ConsumerF[A, X] = One |&| (One |+| (Neg[A] |*| X))
  type Consumer[A] = Rec[ConsumerF[A, *]]

  object LPollable {
    def close[A]: LPollable[A] -⚬ One =
      id                       [   LPollable[A]     ]
        .unpack             .to[ One |&| LPolled[A] ]
        .chooseL            .to[ One                ]

    def poll[A]: LPollable[A] -⚬ LPolled[A] =
      id                       [   LPollable[A]     ]
        .unpack             .to[ One |&| LPolled[A] ]
        .chooseR            .to[         LPolled[A] ]

    /** Polls and discards all elements. */
    def drain[A](implicit A: Comonoid[A]): LPollable[A] -⚬ One =
      rec { self =>
        poll[A] andThen either(id, parToOne(A.counit, self))
      }

    def emptyF[A]: One -⚬ LPollableF[A, LPollable[A]] =
      choice[One, One, LPolled[A]](id, injectL)

    def empty[A]: One -⚬ LPollable[A] =
      emptyF[A].pack

    def concat[A]: (LPollable[A] |*| LPollable[A]) -⚬ LPollable[A] = rec { self =>
      val close: (LPollable[A] |*| LPollable[A]) -⚬ One =
        parToOne(LPollable.close, LPollable.close)

      val poll: (LPollable[A] |*| LPollable[A]) -⚬ LPolled[A] =
        id                             [                               LPollable[A]    |*| LPollable[A]        ]
          .in.fst(unpack)           .to[ (One |&| (One |+| (A |*| LPollable[A]))) |*| LPollable[A]             ]
          .in.fst(chooseR)          .to[          (One |+| (A |*| LPollable[A]))  |*| LPollable[A]             ]
          .distributeRL             .to[ (One |*| LPollable[A])  |+| ((A |*|  LPollable[A]) |*| LPollable[A])  ]
          .in.left(elimFst)         .to[          LPollable[A]   |+| ((A |*|  LPollable[A]) |*| LPollable[A])  ]
          .in.left(LPollable.poll)  .to[           LPolled[A]    |+| ((A |*|  LPollable[A]) |*| LPollable[A])  ]
          .in.right(timesAssocLR)   .to[           LPolled[A]    |+| ( A |*| (LPollable[A]  |*| LPollable[A])) ]
          .in.right.snd(self)       .to[           LPolled[A]    |+| ( A |*|            LPollable[A]         ) ]
          .in.right.injectR[One]    .to[           LPolled[A]    |+|     LPolled[A]                            ]
          .andThen(either(id, id))  .to[                     LPolled[A]                                        ]

      choice(close, poll)
        .pack[LPollableF[A, *]]
    }
  }

  object Pollable {
    def close[A]: Pollable[A] -⚬ One =
      LPollable.close[Val[A]]

    def poll[A]: Pollable[A] -⚬ Polled[A] =
      LPollable.poll[Val[A]]

    /** Polls and discards all elements. */
    def drain[A]: Pollable[A] -⚬ One =
      LPollable.drain[Val[A]]

    def emptyF[A]: One -⚬ PollableF[A, Pollable[A]] =
      LPollable.emptyF[Val[A]]

    def empty[A]: One -⚬ Pollable[A] =
      LPollable.empty[Val[A]]

    def fromList[A]: Val[List[A]] -⚬ Pollable[A] = rec { self =>
      val uncons: List[A] => Option[(A, List[A])] = _ match {
        case a :: as => Some((a, as))
        case Nil => None
      }

      val close: Val[List[A]] -⚬ One = discard

      val poll: Val[List[A]] -⚬ Polled[A] =
        liftV(uncons)                           .to[ Val[Option[(A, List[A])]] ]
          .andThen(Maybe.liftOption)            .to[ One |+| Val[(A, List[A])] ]
          .in.right(liftPair)                   .to[ One |+| (Val[A] |*| Val[List[A]]) ]
          .in.right.snd(self)                   .to[ One |+| (Val[A] |*| Pollable[A] ) ]

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    def prepend[A]: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] = {
      val close: (Val[A] |*| Pollable[A]) -⚬ One =
        parToOne(discard, Pollable.close)

      val poll: (Val[A] |*| Pollable[A]) -⚬ Polled[A] =
        injectR

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    def concat[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.concat[Val[A]]

    /** Merges two [[Pollable]]s into one. When there is a value available from both upstreams, favors the first one. */
    def merge[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] = rec { self =>
      val close: (Pollable[A] |*| Pollable[A]) -⚬ One =
        parToOne(Pollable.close, Pollable.close)

      val unpoll: Polled[A] -⚬ Pollable[A] = {
        val closePolled: Polled[A] -⚬ One =
          either(id, parToOne(discard, Pollable.close))

        choice(closePolled, id[Polled[A]])
          .pack[PollableF[A, *]]
      }

      // checks the first argument first, uses the given function for recursive calls
      def go(merge: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A]): (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        id[Polled[A] |*| Polled[A]]   .to[ (One |+| (Val[A] |*| Pollable[A])) |*| Polled[A]                   ]
          .distributeRL               .to[ (One |*| Polled[A]) |+| ((Val[A] |*| Pollable[A]) |*|  Polled[A] ) ]
          .in.left(elimFst)           .to[          Polled[A]  |+| ((Val[A] |*| Pollable[A]) |*|  Polled[A] ) ]
          .in.right.snd(unpoll)       .to[          Polled[A]  |+| ((Val[A] |*| Pollable[A]) |*| Pollable[A]) ]
          .in.right(timesAssocLR)     .to[          Polled[A]  |+| (Val[A] |*| (Pollable[A] |*| Pollable[A])) ]
          .in.right.snd(merge)        .to[          Polled[A]  |+| (Val[A] |*|          Pollable[A]         ) ]
          .in.right.injectR[One]      .to[          Polled[A]  |+|       Polled[A]                            ]
          .andThen(either(id, id))    .to[                  Polled[A]                                         ]

      // checks the first argument first
      val goFst: (Polled[A] |*| Polled[A]) -⚬ Polled[A] = go(self)

      // checks the second argument first
      val goSnd: (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        swap[Polled[A], Polled[A]]
          .andThen(go(swap[Pollable[A], Pollable[A]] andThen self))

      val poll: (Pollable[A] |*| Pollable[A]) -⚬ Polled[A] =
        id[Pollable[A] |*| Pollable[A]]               .to[ Pollable[A] |*| Pollable[A]                               ]
          .par(Pollable.poll[A], Pollable.poll[A])    .to[  Polled[A]  |*|  Polled[A]                                ]
          .andThen(race)                              .to[ (Polled[A]  |*|  Polled[A]) |+| (Polled[A] |*| Polled[A]) ]
          .either(goFst, goSnd)                       .to[                          Polled[A]                        ]

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    // TODO: polish
    def dup[A]: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) = rec { self =>
      // the case when the first output polls or closes before the second output does
      val caseFst: Pollable[A] -⚬ ((One |&| Polled[A]) |*| (One |&| Polled[A])) = {
        val caseFstClosed: Pollable[A] -⚬ (One |*| (One |&| Polled[A])) =
          id[ Pollable[A] ]     .to[            Pollable[A]      ]
            .unpack             .to[          One |&| Polled[A]  ]
            .introFst           .to[ One |*| (One |&| Polled[A]) ]

        val caseFstPolled: Pollable[A] -⚬ (Polled[A] |*| (One |&| Polled[A])) = {
          val caseUpstreamClosed: One -⚬ (Polled[A] |*| (One |&| Polled[A])) = {
            val closedPolled: One -⚬ Polled[A] = injectL
            parFromOne(closedPolled, choice(id, closedPolled))
          }

          val caseUpstreamValue:  (Val[A] |*| Pollable[A]) -⚬ (Polled[A] |*| (One |&| Polled[A])) = {
            val goSnd: (Val[A] |*| Pollable[A]) -⚬ (Pollable[A] |*| (One |&| Polled[A])) = {
              val sndClosed: (Val[A] |*| Pollable[A]) -⚬ (Pollable[A] |*| One) =
                swap[Val[A], Pollable[A]]     .from[ Val[A] |*| Pollable[A] ]
                  .to  [ Pollable[A] |*| Val[A] ]
                  .in.snd(discard)            .to  [ Pollable[A] |*|  One   ]

              val sndPolled: (Val[A] |*| Pollable[A]) -⚬ (Pollable[A] |*| Polled[A]) =
                id[ Val[A] |*| Pollable[A] ]
                  .in.snd(self)         .to[ Val[A] |*| (Pollable[A] |*| Pollable[A]) ]
                  .timesAssocRL         .to[ (Val[A] |*| Pollable[A]) |*| Pollable[A] ]
                  .in.fst(swap)         .to[ (Pollable[A] |*| Val[A]) |*| Pollable[A] ]
                  .timesAssocLR         .to[ Pollable[A] |*| (Val[A] |*| Pollable[A]) ]
                  .in.snd.injectR[One]  .to[ Pollable[A] |*|      Polled[A]           ]

              choice(sndClosed, sndPolled)  .from[ Val[A] |*| Pollable[A] ]
                .to  [ (Pollable[A] |*| One) |&| (Pollable[A] |*| Polled[A]) ]
                .andThen(coDistributeL)     .to  [ Pollable[A] |*| (One |&| Polled[A])                   ]
            }

            id                               [        Val[A]       |*| Pollable[A]              ]
              .in.fst(dsl.dup)            .to[ (Val[A] |*| Val[A]) |*| Pollable[A]              ]
              .timesAssocLR               .to[ Val[A] |*| (Val[A] |*| Pollable[A])              ]
              .in.snd(goSnd)              .to[ Val[A] |*| (Pollable[A] |*| (One |&| Polled[A])) ]
              .timesAssocRL               .to[ (Val[A] |*| Pollable[A]) |*| (One |&| Polled[A]) ]
              .in.fst.injectR[One]        .to[      Polled[A]           |*| (One |&| Polled[A]) ]
          }

          Pollable.poll[A]                                  .from[          Pollable[A]              ]
            .to  [ One |+| (Val[A] |*| Pollable[A])  ]
            .either(caseUpstreamClosed, caseUpstreamValue)  .to  [ Polled[A] |*| (One |&| Polled[A]) ]
        }

        choice(caseFstClosed, caseFstPolled)  .from[                          Pollable[A]                                  ]
          .to  [ (One |*| (One |&| Polled[A])) |&| (Polled[A] |*| (One |&| Polled[A])) ]
          .andThen(coDistributeR)             .to  [ (One |&| Polled[A]) |*| (One |&| Polled[A])                           ]
      }

      // the case when the second output polls or closes before the first output does
      val caseSnd: Pollable[A] -⚬ ((One |&| Polled[A]) |*| (One |&| Polled[A])) =
        caseFst andThen swap

      id[Pollable[A]]                                       .to[                                           Pollable[A]                                           ]
        .choice(caseFst, caseSnd)                           .to[ ((One |&| Polled[A]) |*| (One |&| Polled[A])) |&| ((One |&| Polled[A]) |*| (One |&| Polled[A])) ]
        .andThen(select)                                    .to[                           (One |&| Polled[A]) |*| (One |&| Polled[A])                           ]
        .par(pack[PollableF[A, *]], pack[PollableF[A, *]])  .to[                              Pollable[A]      |*|    Pollable[A]                                ]
    }

    def dropUntilFirstDemand[A]: Pollable[A] -⚬ Pollable[A] = {
      val goUnpacked: (One |&| Polled[A]) -⚬ (One |&| Polled[A]) = rec { self =>
        val caseDownstreamRequested: (Val[A] |*| Pollable[A]) -⚬ (One |&| Polled[A]) = {
          val caseDownstreamClosed: (Val[A] |*| Pollable[A]) -⚬ One       = parToOne(discard, Pollable.close)
          val caseDownstreamPulled: (Val[A] |*| Pollable[A]) -⚬ Polled[A] = injectR
          choice(caseDownstreamClosed, caseDownstreamPulled)
        }

        val caseNotRequestedYet: (Val[A] |*| Pollable[A]) -⚬ (One |&| Polled[A]) = {
          id[Val[A] |*| Pollable[A]]
            .andThen(discardFst)
            .unpack
            .andThen(self)
        }

        val goElem: (Val[A] |*| Pollable[A]) -⚬ (One |&| Polled[A]) =
          choice(caseDownstreamRequested, caseNotRequestedYet)
            .andThen(selectRequestedOrNot)

        id                               [ One |&| Polled[A]                ]
          .chooseR                    .to[ One |+| (Val[A] |*| Pollable[A]) ]
          .either(emptyF[A], goElem)  .to[ One |&| Polled[A]                ]
      }

      unpack[PollableF[A, *]]
        .andThen(goUnpacked)
        .pack[PollableF[A, *]]
    }

    def broadcast[A]: Pollable[A] -⚬ Unlimited[Pollable[A]] = rec { self =>
      val case0: Pollable[A] -⚬ One                                                 = Pollable.close
      val case1: Pollable[A] -⚬ Pollable[A]                                         = id
      val caseN: Pollable[A] -⚬ (Unlimited[Pollable[A]] |*| Unlimited[Pollable[A]]) = dup andThen par(self, self)

      dropUntilFirstDemand
        .choice(case0, (choice(case1, caseN)))
        .pack[UnlimitedF[Pollable[A], *]]
    }
  }

  implicit def consumerProducingDuality[A]: Dual[Consumer[A], Producing[A]] =
    dualRec[ConsumerF[A, *], ProducingF[A, *]](
      new Dual1[ConsumerF[A, *], ProducingF[A, *]] {
        def apply[x, y]: Dual[x, y] => Dual[ConsumerF[A, x], ProducingF[A, y]] = { xy_dual =>
          choiceEitherDuality(
            Dual[One, One],
            eitherChoiceDuality(
              Dual[One, One],
              productDuality(
                Dual[Neg[A], Val[A]],
                xy_dual
              )
            )
          )
        }
      }
    )

  implicit def producingConsumerDuality[A]: Dual[Producing[A], Consumer[A]] =
    dualSymmetric(consumerProducingDuality[A])

  implicit def subscriberPollableDuality[A, B](implicit AB: Dual[A, B]): Dual[LSubscriber[A], LPollable[B]] =
    dualRec[LSubscriberF[A, *], LPollableF[B, *]](
      new Dual1[LSubscriberF[A, *], LPollableF[B, *]] {
        def apply[x, y]: Dual[x, y] => Dual[LSubscriberF[A, x], LPollableF[B, y]] = { xy_dual =>
          eitherChoiceDuality(
            Dual[One, One],
            choiceEitherDuality(
              Dual[One, One],
              productDuality(
                AB,
                xy_dual
              )
            )
          )
        }
      }
    )

  implicit def pollableSubscriberDuality[A, B](implicit BA: Dual[B, A]): Dual[LPollable[A], LSubscriber[B]] =
    dualSymmetric(subscriberPollableDuality[B, A])

  /** If either the source or the sink is completed, complete the other one and be done.
    * Otherwise, expose their offer and demand, respectively.
    */
  def relayCompletion[A, B]: (Pollable[A] |*| Subscriber[B]) -⚬ (One |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B]))) =
    id                                [ Pollable[A] |*| (                    Subscriber[B]                                  )]
      .in.snd(unpack)              .to[ Pollable[A] |*| (One     |+|                    (One |&| (Neg[B] |*| Subscriber[B])))]
      .distributeLR                .to[(Pollable[A] |*|  One)    |+| (Pollable[A]   |*| (One |&| (Neg[B] |*| Subscriber[B])))]
      .in.left(elimSnd)            .to[ Pollable[A]              |+| (Pollable[A]   |*| (One |&| (Neg[B] |*| Subscriber[B])))]
      .in.left(Pollable.close)     .to[ One |+|                      (Pollable[A]   |*| (One |&| (Neg[B] |*| Subscriber[B])))]
      .in.right.fst(Pollable.poll) .to[ One |+| ((One |+| (Val[A] |*| Pollable[A])) |*| (One |&| (Neg[B] |*| Subscriber[B])))]
      .in.right(matchingChoiceLR)  .to[ One |+| ((One |*| One) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])))]
      .in.right.left(elimSnd)      .to[ One |+| (     One      |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])))]
      .plusAssocRL                 .to[(One |+|       One    ) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]
      .in.left(either(id, id))     .to[     One                |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]

  type Source[A] = One -⚬ Pollable[A]
  object Source {
    def empty[A]: Source[A] = {
      choice(id[One], injectL[One, Val[A] |*| Pollable[A]])
        .pack[PollableF[A, *]]
    }

    def singleton[A](a: A): Source[A] = {
      val poll: One -⚬ (One |+| (Val[A] |*| Pollable[A])) =
        parFromOne(const(a), Source.empty[A]) .from[                 One              ]
          .to  [          Val[A] |*| Pollable[A]  ]
          .injectR                            .to  [ One |+| (Val[A] |*| Pollable[A]) ]

      choice(id[One], poll)
        .pack[PollableF[A, *]]
    }

    def fromList[A](elems: List[A]): Source[A] = {
      const(elems) andThen Pollable.fromList[A]
    }

    def concat[A](src1: Source[A], src2: Source[A]): Source[A] = {
      parFromOne(src1, src2)
        .andThen(Pollable.concat[A])
    }
  }

  type Pipe[A, B] = Pollable[A] -⚬ Pollable[B]
  object Pipe {
    def lift[A, B](f: A => B): Pipe[A, B] = {
      val ff: Val[A] -⚬ Val[B] = liftV(f)

      rec(self =>
        id[Pollable[A]]                     .to[   Pollable[A]                              ]
          .unpack                           .to[ One |&| (One |+| (Val[A] |*| Pollable[A])) ]
          .in.choiceR.right.fst(ff)         .to[ One |&| (One |+| (Val[B] |*| Pollable[A])) ]
          .in.choiceR.right.snd(self)       .to[ One |&| (One |+| (Val[B] |*| Pollable[B])) ]
          .pack[PollableF[B, *]]            .to[                              Pollable[B]   ]
      )
    }

    def statefulMap[S, A, B](f: ((S, A)) => (S, B))(initialState: S): Pipe[A, B] = {
      val ff: (Val[S] |*| Val[A]) -⚬ (Val[S] |*| Val[B]) =
        unliftPair[S, A]
          .andThen(liftV(f))
          .andThen(liftPair[S, B])

      val inner: (Val[S] |*| Pollable[A]) -⚬ Pollable[B] = rec { self =>
        val close: (Val[S] |*| Pollable[A]) -⚬ One =
          parToOne(discard, Pollable.close)

        val poll:(Val[S] |*| Pollable[A]) -⚬ (One |+| (Val[B] |*| Pollable[B])) =
          id[Val[S] |*| Pollable[A]]          .to[ Val[S] |*|                      Pollable[A]   ]
            .in.snd(Pollable.poll)            .to[ Val[S] |*| (One |+| (Val[A] |*| Pollable[A])) ]
            .distributeLR                     .to[ (Val[S] |*| One) |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .in.left(parToOne(discard, id))   .to[         One      |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .in.right(timesAssocRL)           .to[         One      |+| ((Val[S] |*| Val[A]) |*| Pollable[A]) ]
            .in.right.fst(ff)                 .to[         One      |+| ((Val[S] |*| Val[B]) |*| Pollable[A]) ]
            .in.right.fst(swap)               .to[         One      |+| ((Val[B] |*| Val[S]) |*| Pollable[A]) ]
            .in.right(timesAssocLR)           .to[         One      |+| (Val[B] |*| (Val[S] |*| Pollable[A])) ]
            .in.right.snd(self)               .to[         One      |+| (Val[B] |*|     Pollable[B]         ) ]

        choice(close, poll)
          .pack[PollableF[B, *]]
      }

      id[Pollable[A]]                   .to[            Pollable[A] ]
        .introFst(const(initialState))  .to[ Val[S] |*| Pollable[A] ]
        .andThen(inner)                 .to[     Pollable[B]        ]
    }
  }
}
