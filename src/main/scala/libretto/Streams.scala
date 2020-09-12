package libretto

object Streams {
  def apply[DSL <: libretto.DSL](dsl0: DSL)(lib0: Lib[dsl0.type])(bst: BinarySearchTree[dsl0.type]): Streams[DSL] =
    new Streams[DSL] {
      val dsl: dsl0.type = dsl0
      val lib = lib0
      val Tree = bst
    }
}

sealed trait Streams[DSL <: libretto.DSL] {
  val dsl: DSL
  val lib: Lib[dsl.type]
  val Tree: BinarySearchTree[dsl.type]

  import dsl._
  import lib._
  import Tree._

  type LPollableF[A, X] = One |&| (One |+| (A |*| X))
  type LPollable[A] = Rec[LPollableF[A, *]]
  type LPolled[A] = One |+| (A |*| LPollable[A])

  type PollableF[A, X] = LPollableF[Val[A], X]
  type Pollable[A] = LPollable[Val[A]]
  type Polled[A] = LPolled[Val[A]]

  type LSubscriberF[A, X]  = One |+| (One |&| (A |*| X))
  type LSubscriber[A] = Rec[LSubscriberF[A, *]]
  type LDemanding[A] = One |&| (A |*| LSubscriber[A])

  type SubscriberF[A, X]  = LSubscriberF[Neg[A], X]
  type Subscriber[A] = LSubscriber[Neg[A]]
  type Demanding[A] = LDemanding[Neg[A]]

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
        id[Pollable[A] |*| Pollable[A]]               .to[ Pollable[A] |*| Pollable[A] ]
          .par(Pollable.poll[A], Pollable.poll[A])    .to[  Polled[A]  |*|  Polled[A]  ]
          .race(goFst, goSnd)                         .to[           Polled[A]         ]

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    implicit def requisitivePollable[A]: Requisitive1[PollableF[A, *]] =
      new Requisitive1[PollableF[A, *]] {
        def apply[X]: Requisitive[PollableF[A, X]] = implicitly
      }

    def dup[A]: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) = rec { self =>
      val dupPolled: Polled[A] -⚬ (Polled[A] |*| Polled[A]) = {
        val caseClosed: One -⚬ (Polled[A] |*| Polled[A]) =
          parFromOne(injectL, injectL)

        val caseValue: (Val[A] |*| Pollable[A]) -⚬ (Polled[A] |*| Polled[A]) =
          id                                             [        Val[A]       |*|          Pollable[A]          ]
            .par(dsl.dup[A], self)                    .to[ (Val[A] |*| Val[A]) |*| (Pollable[A] |*| Pollable[A]) ]
            .andThen(IXI)                             .to[ (Val[A] |*| Pollable[A]) |*| (Val[A] |*| Pollable[A]) ]
            .in.fst.injectR[One].in.snd.injectR[One]  .to[       Polled[A]          |*|       Polled[A]          ]

        either(caseClosed, caseValue)
      }

      val caseFstClosed: Pollable[A] -⚬ (One |*| Pollable[A]) =
        introFst

      val caseFstPolled: Pollable[A] -⚬ (Polled[A] |*| Pollable[A]) =
        id                                           [                 Pollable[A]                       ]
          .andThen(Pollable.poll[A])              .to[                  Polled[A]                        ]
          .andThen(choice(introSnd, dupPolled))   .to[ (Polled[A] |*| One) |&| (Polled[A] |*| Polled[A]) ]
          .andThen(coDistributeL)                 .to[  Polled[A] |*| (One |&|                Polled[A]) ]
          .in.snd(pack[PollableF[A, *]])          .to[  Polled[A] |*|      Pollable[A]                   ]

      // the case when the first output polls or closes before the second output does
      val caseFst: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) =
        id                                           [                  Pollable[A]                           ]
          .choice(caseFstClosed, caseFstPolled)   .to[ (One |*| Pollable[A]) |&| (Polled[A]  |*| Pollable[A]) ]
          .andThen(coDistributeR)                 .to[ (One                  |&|  Polled[A]) |*| Pollable[A]  ]
          .in.fst(pack[PollableF[A, *]])          .to[             Pollable[A]               |*| Pollable[A]  ]

      // the case when the second output polls or closes before the first output does
      val caseSnd: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) =
        caseFst andThen swap

      id                                   [          Pollable[A]        ]
        .select(caseFst, caseSnd)       .to[ Pollable[A] |*| Pollable[A] ]
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

    private[Pollable] type DemandingTree[K, V] = Tree[K, Demanding[V]]
    private[Pollable] object DemandingTree {
      type DT[K, V] = DemandingTree[K, V]
      type NeDT[K, V] = NonEmptyTree[K, Demanding[V]]

      def dispatch[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| DT[K, V]) -⚬ (Maybe[Val[V]] |*| DT[K, V]) =
        Tree.update(Demanding.supply[V])

      def dispatchNE[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| NeDT[K, V]) -⚬ (Maybe[NeDT[K, V]]) =
        NonEmptyTree.update(Demanding.supply[V])
          .elimFst(Maybe.discard[Val[V]])

      def dispatchNE[A, K: Ordering, V](
        f: Val[A] -⚬ (Val[K] |*| Val[V]),
      ): Val[A] |*| NeDT[K, V] -⚬ Maybe[NeDT[K, V]] =
        id                                     [       Val[A]        |*| NeDT[K, V]  ]
          .in.fst(f)                        .to[ (Val[K] |*| Val[V]) |*| NeDT[K, V]  ]
          .andThen(dispatchNE)              .to[                   Maybe[NeDT[K, V]] ]

      def addDemanding[K: Ordering, V]: (Val[K] |*| Demanding[V]) |*| DT[K, V] -⚬ DT[K, V] =
        Tree.insertOrUpdate(Demanding.merge)

      def clear[K, V]: DT[K, V] -⚬ One =
        Tree.clear(Demanding.close)

      def addSubscriber[K: Ordering, V]: (Val[K] |*| Subscriber[V]) |*| DT[K, V] -⚬ DT[K, V] =
        id                                           [ ( Val[K] |*|       Subscriber[V]               ) |*| DT[K, V] ]
          .in.fst.snd(unpack)                     .to[ ( Val[K] |*| (One |+|             Demanding[V])) |*| DT[K, V] ]
          .in.fst(distributeLR)                   .to[ ((Val[K] |*| One) |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .in.fst.left(elimFst(discard))          .to[ (        One      |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .distributeRL
          .either(elimFst, addDemanding)
    }

    // TODO: ensure backpressure on slow subscribers
    def subscribeByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): (Pollable[A] |*| LPollable[Val[K] |*| Subscriber[V]]) -⚬ One = {
      import Pollable.{DemandingTree => DT}
      type KSubs = Val[K] |*| Subscriber[V]

      val upstreamClosed: One |*| (LPolled[KSubs] |*| Tree[K, Demanding[V]]) -⚬ One =
        elimFst >>> parToOne(LPolled.close(parToOne(dsl.discard, Subscriber.close)), DT.clear)

      def upstreamVal(
        goRec: (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One,
      ): (Val[A] |*| Pollable[A]) |*| (LPolled[KSubs] |*| Tree[K, Demanding[V]]) -⚬ One =
        id                                   [ (Val[A] |*| Pollable[A]) |*|              (LPolled[KSubs] |*| Tree[K, Demanding[V]]) ]
          .in.fst(swap)                   .to[ (Pollable[A] |*| Val[A]) |*|              (LPolled[KSubs] |*| Tree[K, Demanding[V]]) ]
          .andThen(IXI)                   .to[ (Pollable[A] |*| LPolled[KSubs]) |*| (      Val[A]        |*| Tree[K, Demanding[V]]) ]
          .in.snd.fst(f)                  .to[ (Pollable[A] |*| LPolled[KSubs]) |*| ((Val[K] |*| Val[V]) |*| Tree[K, Demanding[V]]) ]
          .in.snd(DT.dispatch)            .to[ (Pollable[A] |*| LPolled[KSubs]) |*| (   Maybe[Val[V]]    |*| Tree[K, Demanding[V]]) ]
          .in.snd(elimFst(Maybe.discard)) .to[ (Pollable[A] |*| LPolled[KSubs]) |*|                          Tree[K, Demanding[V]]  ]
          .in.fst.fst(poll)               .to[ (  Polled[A] |*| LPolled[KSubs]) |*|                          Tree[K, Demanding[V]]  ]
          .andThen(goRec)                 .to[                                  One                                                 ]

      def onUpstream(
        goRec: (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One,
      ): (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One =
        timesAssocLR      .to[ Polled[A] |*| (LPolled[KSubs] |*| Tree[K, Demanding[V]]) ]
          .distributeRL
          .either(upstreamClosed, upstreamVal(goRec))

      val forward: Polled[A] |*| Tree[K, Demanding[V]] -⚬ One = {
        id                                               [  Polled[A] |*| (One |+|                NonEmptyTree[K, Demanding[V]]) ]
          .distributeLR                               .to[ (Polled[A] |*| One) |+| (Polled[A] |*| NonEmptyTree[K, Demanding[V]]) ]
          .in.left(elimFst(Polled.close))             .to[            One      |+| (Polled[A] |*| NonEmptyTree[K, Demanding[V]]) ]
          .in.right(LPolled.feedTo(DT.dispatchNE(f))) .to[            One      |+|          Maybe[NonEmptyTree[K, Demanding[V]]] ]
          .in.right(DT.clear)                         .to[            One      |+|            One                                ]
          .andThen(either(id, id))                    .to[                     One                                               ]
      }

      val subsClosed: (Polled[A] |*| One) |*| Tree[K, Demanding[V]] -⚬ One =
        par(elimSnd[Polled[A]], id[Tree[K, Demanding[V]]]) >>> forward

      def newSubscriber(
        goRec: (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One,
      ): (Polled[A] |*| (KSubs |*| LPollable[KSubs])) |*| Tree[K, Demanding[V]] -⚬ One =
        id                               [ (Polled[A] |*| (KSubs |*| LPollable[KSubs])) |*| Tree[K, Demanding[V]] ]
        .in.fst.snd(swap)             .to[ (Polled[A] |*| (LPollable[KSubs] |*| KSubs)) |*| Tree[K, Demanding[V]] ]
        .in.fst(timesAssocRL)         .to[ ((Polled[A] |*| LPollable[KSubs]) |*| KSubs) |*| Tree[K, Demanding[V]] ]
        .timesAssocLR                 .to[ (Polled[A] |*| LPollable[KSubs]) |*| (KSubs |*| Tree[K, Demanding[V]]) ]
        .in.snd(DT.addSubscriber)     .to[ (Polled[A] |*| LPollable[KSubs]) |*|            Tree[K, Demanding[V]]  ]
        .in.fst.snd(LPollable.poll)   .to[ (Polled[A] |*|   LPolled[KSubs]) |*|            Tree[K, Demanding[V]]  ]
        .andThen(goRec)

      def onSubs(
        goRec: (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One,
      ): (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One =
        id[ (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] ]
          .in.fst(distributeLR)
          .distributeRL
          .either(subsClosed, newSubscriber(goRec))

      val go: (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] -⚬ One = rec { self =>
        id                                           [ (Polled[A] |*| LPolled[KSubs]) |*| Tree[K, Demanding[V]] ]
          .in.fst(race)
          .distributeRL
          .either(onUpstream(self), onSubs(self)) .to[                                One                       ]
        }

      id[Pollable[A] |*| LPollable[KSubs]]
        .andThen(par(poll, LPollable.poll))
        .introSnd(Tree.empty[K, Demanding[V]])
        .andThen(go)
    }
  }

  object LPolled {
    def close[A](discard: A -⚬ One): LPolled[A] -⚬ One =
      either(id, parToOne(discard, LPollable.close))

    def feedTo[A, B](f: A |*| B -⚬ Maybe[B]): LPolled[A] |*| B -⚬ Maybe[B] = rec { self =>
      val upstreamClosed: One |*| B -⚬ Maybe[B] =
        elimFst[B] >>> Maybe.just

      val upstreamValue: (A |*| LPollable[A]) |*| B -⚬ Maybe[B] =
        id                                             [ (     A       |*| LPollable[A]) |*| B           ]
          .in.fst(swap)                             .to[ (LPollable[A] |*|      A      ) |*| B           ]
          .timesAssocLR                             .to[  LPollable[A] |*|     (A        |*| B)          ]
          .in.snd(f)                                .to[  LPollable[A] |*|          Maybe[B]             ]
          .distributeLR                             .to[ (LPollable[A] |*| One) |+| (LPollable[A] |*| B) ]
          .in.left.fst(LPollable.close)             .to[ (         One |*| One) |+| (LPollable[A] |*| B) ]
          .in.left(elimFst[One] >>> Maybe.empty[B]) .to[           Maybe[B]     |+| (LPollable[A] |*| B) ]
          .in.right.fst(LPollable.poll)             .to[           Maybe[B]     |+| (  LPolled[A] |*| B) ]
          .in.right(self)                           .to[           Maybe[B]     |+|           Maybe[B]   ]
          .andThen(either(id, id))                  .to[                      Maybe[B]                   ]

      id[ (One |+| (A |*| LPollable[A])) |*| B ]
        .distributeRL
        .either(upstreamClosed, upstreamValue)
    }
  }

  object Polled {
    def close[A]: Polled[A] -⚬ One =
      LPolled.close(dsl.discard[A])
  }

  object LSubscriber {
    def close[A]: LSubscriber[A] -⚬ One =
      unpack[LSubscriberF[A, *]] >>> either(id, chooseL)
  }

  object Subscriber {
    implicit def completiveSubscriberF[A]: Completive1[SubscriberF[A, *]] =
      new Completive1[SubscriberF[A, *]] {
        def apply[X]: Completive[SubscriberF[A, X]] = implicitly
      }

    def close[A]: Subscriber[A] -⚬ One =
      LSubscriber.close

    private[Streams] def merge[A](
      mergeDemandings: (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A]
    ): (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] = {
      val fstClosed: (One |*| Subscriber[A]) -⚬ Subscriber[A] =
        elimFst

      val fstDemanding: (Demanding[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        id                                               [  Demanding[A] |*|      Subscriber[A]                       ]
          .in.snd(unpack)                             .to[  Demanding[A] |*| (One |+|                   Demanding[A]) ]
          .distributeLR                               .to[ (Demanding[A] |*| One) |+| (Demanding[A] |*| Demanding[A]) ]
          .andThen(either(elimSnd, mergeDemandings))  .to[                    Demanding[A]                            ]
          .injectR[One].pack[SubscriberF[A, *]]       .to[                   Subscriber[A]                            ]

      val caseFstReady: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        id                                     [      Subscriber[A]                         |*| Subscriber[A]  ]
          .in.fst(unpack)                   .to[ (One |+|                     Demanding[A]) |*| Subscriber[A]  ]
          .distributeRL                     .to[ (One |*| Subscriber[A]) |+| (Demanding[A]  |*| Subscriber[A]) ]
          .either(fstClosed, fstDemanding)  .to[                    Subscriber[A]                              ]

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
    def supply[A, B](implicit ev: Dual[A, B]): (A |*| LDemanding[B]) -⚬ Maybe[LDemanding[B]] =
      id[ A |*| LDemanding[B] ]     .to[ A |*| (One |&| (B |*| LSubscriber[B])) ]
      .in.snd(chooseR)              .to[ A |*|          (B |*| LSubscriber[B])  ]
      .timesAssocRL                 .to[ (A |*| B)         |*| LSubscriber[B]   ]
      .elimFst(ev.rInvert)        .to[                       LSubscriber[B]   ]
      .unpack[LSubscriberF[B, *]]   .to[                   Maybe[LDemanding[B]] ]
  }

  object Demanding {
    def close[A]: Demanding[A] -⚬ One =
      chooseL

    def supply[A]: (Val[A] |*| Demanding[A]) -⚬ Maybe[Demanding[A]] =
      LDemanding.supply[Val[A], Neg[A]]

    private[Streams] def merge[A](
      mergeSubscribers: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A]
    ): (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A] = {
      val caseClosed: (Demanding[A] |*| Demanding[A]) -⚬ One =
        parToOne(chooseL, chooseL)

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
  }

  def rInvertProducingF[A, x, y](rInvertSub: (x |*| y) -⚬ One): (ProducingF[A, x] |*| ConsumerF[A, y]) -⚬ One =
    rInvertEither(
      Dual[One, One].rInvert,
      swap >>> rInvertEither(
        Dual[One, One].rInvert,
        rInvertTimes(
          swap >>> fulfill[A],
          swap >>> rInvertSub
        )
      )
    )

  def lInvertConsumerF[A, x, y](lInvertSub: One -⚬ (y |*| x)): One -⚬ (ConsumerF[A, y] |*| ProducingF[A, x]) =
    lInvertChoice(
      Dual[One, One].lInvert,
      lInvertChoice(
        Dual[One, One].lInvert,
        lInvertTimes(
          promise[A] >>> swap,
          lInvertSub >>> swap
        )
      ) >>> swap
    )

  implicit def producingConsumerDuality[A]: Dual[Producing[A], Consumer[A]] =
    dualRec[ProducingF[A, *], ConsumerF[A, *]](
      new Dual1[ProducingF[A, *], ConsumerF[A, *]] {
        def apply[x, y]: Dual[x, y] => Dual[ProducingF[A, x], ConsumerF[A, y]] = { xy_dual =>
          new Dual[ProducingF[A, x], ConsumerF[A, y]] {
            val rInvert: (ProducingF[A, x] |*| ConsumerF[A, y]) -⚬ One = rInvertProducingF(xy_dual.rInvert)
            val lInvert: One -⚬ (ConsumerF[A, y] |*| ProducingF[A, x]) = lInvertConsumerF (xy_dual.lInvert)
          }
        }
      }
    )

  implicit def consumerProducingDuality[A]: Dual[Consumer[A], Producing[A]] =
    dualSymmetric(producingConsumerDuality[A])

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
        parFromOne(const_(a), Source.empty[A])  .from[                 One              ]
                                                .to  [          Val[A] |*| Pollable[A]  ]
          .injectR                              .to  [ One |+| (Val[A] |*| Pollable[A]) ]

      choice(id[One], poll)
        .pack[PollableF[A, *]]
    }

    def fromList[A](elems: List[A]): Source[A] = {
      const_(elems) andThen Pollable.fromList[A]
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
        .introFst(const_(initialState)) .to[ Val[S] |*| Pollable[A] ]
        .andThen(inner)                 .to[     Pollable[B]        ]
    }
  }
}
