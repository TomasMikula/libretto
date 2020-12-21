package libretto

object ScalaStreams {
  def apply(
    dsl: ScalaDSL,
    coreLib: CoreLib[dsl.type],
    scalaLib: ScalaLib[dsl.type, coreLib.type],
    coreStreams: CoreStreams[dsl.type, coreLib.type],
  )
  : ScalaStreams[dsl.type, coreLib.type, scalaLib.type, coreStreams.type] =
    new ScalaStreams(dsl, coreLib, scalaLib, coreStreams)
}

class ScalaStreams[
  DSL <: ScalaDSL,
  Lib <: CoreLib[DSL],
  SLib <: ScalaLib[DSL, Lib],
  Streams <: CoreStreams[DSL, Lib],
](
  val dsl: DSL,
  val coreLib: Lib with CoreLib[dsl.type],
  val scalaLib: SLib with ScalaLib[dsl.type, coreLib.type],
  val coreStreams: Streams with CoreStreams[dsl.type, coreLib.type],
) {
  private val Tree = BinarySearchTree(dsl, coreLib, scalaLib)

  import dsl._
  import coreLib._
  import scalaLib._
  import coreStreams._
  import Tree._

  type PollableF[A, X] = LPollableF[Val[A], X]
  type Pollable[A] = LPollable[Val[A]]
  type Polled[A] = LPolled[Val[A]]

  type SubscriberF[A, X]  = LSubscriberF[Neg[A], X]
  type Subscriber[A] = LSubscriber[Neg[A]]
  type Demanding[A] = LDemanding[Neg[A]]

  type ProducingF[A, X]  = Done |+| (Done |&| (Val[A] |*| X))
  type Producing[A] = Rec[ProducingF[A, *]]

  type ConsumerF[A, X] = Need |&| (Need |+| (Neg[A] |*| X))
  type Consumer[A] = Rec[ConsumerF[A, *]]

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
          .andThen(optionToPMaybe)              .to[ Done |+|    Val[(A, List[A])]      ]
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

    def statefulMap[S, A, B](f: ((S, A)) => (S, B))(initialState: S): Pollable[A] -⚬ Pollable[B] = {
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
            .in.right.assocRL                 .to[        Done       |+| ((Val[S] |*| Val[A]) |*| Pollable[A]) ]
            .in.right.fst(ff)                 .to[        Done       |+| ((Val[S] |*| Val[B]) |*| Pollable[A]) ]
            .in.right.fst(swap)               .to[        Done       |+| ((Val[B] |*| Val[S]) |*| Pollable[A]) ]
            .in.right.assocLR                 .to[        Done       |+| (Val[B] |*| (Val[S] |*| Pollable[A])) ]
            .in.right.snd(self)               .to[        Done       |+| (Val[B] |*|     Pollable[B]         ) ]

        choice(close, poll)
          .pack[PollableF[B, *]]
      }

      id[Pollable[A]]                   .to[            Pollable[A] ]
        .introFst(const_(initialState)) .to[ Val[S] |*| Pollable[A] ]
        .andThen(inner)                 .to[     Pollable[B]        ]
    }

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
          .in.right.assocLR           .to[           Polled[A]  |+| (Val[A] |*| (Pollable[A] |*| Pollable[A])) ]
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
          .assocRL                        .to[ ((Pollable[A] |*| LPolled[KSubs]) |*| Done)               |*| DT[K, V]  ]
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
          .in.fst.assocRL               .to[ ((Polled[A] |*|  LPollable[KSubs]) |*|  KSubs ) |*| DT[K, V]  ]
          .assocLR                      .to[  (Polled[A] |*|  LPollable[KSubs]) |*| (KSubs   |*| DT[K, V]) ]
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

  object Subscriber {
    implicit def positiveSubscriber[A]: SignalingJunction.Positive[Subscriber[A]] =
      LSubscriber.positiveLSubscriber[Neg[A]]

    def close[A]: Subscriber[A] -⚬ Need =
      LSubscriber.close

    private[ScalaStreams] def merge[A](
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

  object Demanding {
    def close[A]: Demanding[A] -⚬ Need =
      chooseL

    def supply[A]: (Val[A] |*| Demanding[A]) -⚬ (Need |+| Demanding[A]) =
      LDemanding.supply(fulfill[A])

    private[ScalaStreams] def merge[A](
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
      .assocRL                     .to[(One |+|        One     ) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]
      .in.left(either(id, id))     .to[     One                  |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]
}
