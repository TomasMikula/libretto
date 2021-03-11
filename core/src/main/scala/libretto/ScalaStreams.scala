package libretto

import scala.annotation.tailrec
import scala.concurrent.duration.FiniteDuration

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

    def cons[A]: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.cons

    def fromLList[A]: LList[Val[A]] -⚬ Pollable[A] =
      LPollable.fromLList[Val[A]]

    def delay[A]: Pollable[A] -⚬ Delayed[Pollable[A]] =
      LPollable.delay[Val[A]]

    def delayBy[A]: (Done |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.delayBy[Val[A]]

    def delay[A](d: FiniteDuration): Pollable[A] -⚬ Pollable[A] = {
      id                                           [          Pollable[A] ]
        .<(negativePollable[A].signalNeg)     .from[ Need |*| Pollable[A] ]
        .<.fst(delayNeed(d))                  .from[ Need |*| Pollable[A] ]
        .<(negativePollable[A].awaitNeg)      .from[          Pollable[A] ]
    }

    def fromList[A]: Val[List[A]] -⚬ Pollable[A] = rec { self =>
      val uncons: List[A] => Option[(A, List[A])] = _ match {
        case a :: as => Some((a, as))
        case Nil => None
      }

      val close: Val[List[A]] -⚬ Done = neglect

      val poll: Val[List[A]] -⚬ Polled[A] = {
        val caseNil :              Done -⚬ Polled[A] = Polled.empty[A]
        val caseCons: Val[(A, List[A])] -⚬ Polled[A] = liftPair > par(id, self) > Polled.cons
        mapVal(uncons)                          .to[      Val[Option[(A, List[A])]]     ]
          .>(optionToPMaybe)                    .to[      PMaybe[Val[(A, List[A])]]     ]
          .>(PMaybe.switch(caseNil, caseCons))  .to[             Polled[A]              ]
      }

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    def fromList[A](as: List[A]): One -⚬ Pollable[A] = {
      @tailrec def go(ras: List[A], acc: One -⚬ Pollable[A]): One -⚬ Pollable[A] =
        ras match {
          case head :: tail => go(tail, parFromOne(const(head), acc) > Pollable.cons)
          case Nil          => acc
        }

      go(as.reverse, done > Pollable.empty[A])
    }

    def of[A](as: A*): One -⚬ Pollable[A] =
      fromList(as.toList)

    def toList[A]: Pollable[A] -⚬ Val[List[A]] = {
      def go: (Pollable[A] |*| Val[List[A]]) -⚬ Val[List[A]] = rec { self =>
        id                                   [                        Pollable[A]                    |*| Val[List[A]]  ]
          .>.fst(poll)                    .to[ (Done                   |+| (Val[A] |*| Pollable[A])) |*| Val[List[A]]  ]
          .distributeR                    .to[ (Done |*| Val[List[A]]) |+| ((Val[A] |*| Pollable[A]) |*| Val[List[A]]) ]
          .>.left.snd(mapVal(_.reverse))  .to[ (Done |*| Val[List[A]]) |+| ((Val[A] |*| Pollable[A]) |*| Val[List[A]]) ]
          .>.left.awaitFst                .to[           Val[List[A]]  |+| ((Val[A] |*| Pollable[A]) |*| Val[List[A]]) ]
          .>.right.fst(swap)              .to[           Val[List[A]]  |+| ((Pollable[A] |*| Val[A]) |*| Val[List[A]]) ]
          .>.right.assocLR                .to[           Val[List[A]]  |+| (Pollable[A] |*| (Val[A] |*| Val[List[A]])) ]
          .>.right.snd(unliftPair)        .to[           Val[List[A]]  |+| (Pollable[A] |*|    Val[(A, List[A])]     ) ]
          .>.right.snd(mapVal(_ :: _))    .to[           Val[List[A]]  |+| (Pollable[A] |*|      Val[List[A]]        ) ]
          .>.right(self)                  .to[           Val[List[A]]  |+|          Val[List[A]]                       ]
          .either(id, id)                 .to[                     Val[List[A]]                                        ]
      }

      id[Pollable[A]]
        .>(introSnd(const(List.empty[A])))
        .>(go)
    }

    def repeatedly[A](f: Done -⚬ Val[A]): Done -⚬ Pollable[A] =
      LPollable.repeatedly[Val[A]](f)

    def map[A, B](f: A => B): Pollable[A] -⚬ Pollable[B] = {
      val g: Val[A] -⚬ Val[B] = mapVal(f)
      LPollable.map(g)
    }

    def forEachSequentially[A](f: Val[A] -⚬ Done): Pollable[A] -⚬ Done =
      LPollable.forEachSequentially[Val[A]](f)

    def prepend[A]: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] = {
      val close: (Val[A] |*| Pollable[A]) -⚬ Done =
        join(neglect, Pollable.close)

      val poll: (Val[A] |*| Pollable[A]) -⚬ Polled[A] =
        injectR

      choice(close, poll)
        .pack[PollableF[A, *]]
    }

    def concat[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.concat

    def statefulMap[S, A, B](f: ((S, A)) => (S, B))(initialState: S): Pollable[A] -⚬ Pollable[B] = {
      val ff: (Val[S] |*| Val[A]) -⚬ (Val[S] |*| Val[B]) =
        unliftPair[S, A]
          .>(mapVal(f))
          .>(liftPair[S, B])

      val inner: (Val[S] |*| Pollable[A]) -⚬ Pollable[B] = rec { self =>
        val close: (Val[S] |*| Pollable[A]) -⚬ Done =
          join(neglect, Pollable.close)

        val poll:(Val[S] |*| Pollable[A]) -⚬ (Done |+| (Val[B] |*| Pollable[B])) =
          id[Val[S] |*| Pollable[A]]          .to[ Val[S] |*|                                    Pollable[A]   ]
            .>.snd(Pollable.poll)             .to[ Val[S] |*| (Done  |+|             (Val[A] |*| Pollable[A])) ]
            .distributeL                      .to[ (Val[S] |*| Done) |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .>.left(join(neglect, id))        .to[        Done       |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .>.right.assocRL                  .to[        Done       |+| ((Val[S] |*| Val[A]) |*| Pollable[A]) ]
            .>.right.fst(ff)                  .to[        Done       |+| ((Val[S] |*| Val[B]) |*| Pollable[A]) ]
            .>.right.fst(swap)                .to[        Done       |+| ((Val[B] |*| Val[S]) |*| Pollable[A]) ]
            .>.right.assocLR                  .to[        Done       |+| (Val[B] |*| (Val[S] |*| Pollable[A])) ]
            .>.right.snd(self)                .to[        Done       |+| (Val[B] |*|     Pollable[B]         ) ]

        choice(close, poll)
          .pack[PollableF[B, *]]
      }

      id[Pollable[A]]                   .to[            Pollable[A] ]
        .introFst(const(initialState))  .to[ Val[S] |*| Pollable[A] ]
        .>(inner)                       .to[     Pollable[B]        ]
    }

    /** Splits a stream of "`A` or `B`" to a stream of `A` and a stream of `B`.
      *
      * Polls the upstream only after ''both'' downstreams poll.
      * When either of the downstreams closes, the other downstream and the upstream are closed as well.
      */
    def partition[A, B]: Pollable[Either[A, B]] -⚬ (Pollable[A] |*| Pollable[B]) =
      LPollable.map(liftEither[A, B]) > LPollable.partition

    /** Merges two [[Pollable]]s into one.
      * Left-biased: when there is a value available from both upstreams, favors the first one.
      */
    def merge[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.merge[Val[A]]

    /** Merges a list of [[Pollable]]s into a single [[Pollable]].
      * Head-biased: when there is an element available from multiple upstreams, favors the upstream closest to the
      * head of the input list.
      */
    def mergeAll[A]: LList[Pollable[A]] -⚬ Pollable[A] =
      LPollable.mergeAll[Val[A]]

    implicit def negativePollable[A]: SignalingJunction.Negative[Pollable[A]] =
      LPollable.negativeLPollable[Val[A]]

    def dup[A]: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) = rec { self =>
      val dupPolled: Polled[A] -⚬ (Polled[A] |*| Polled[A]) = {
        val caseClosed: Done -⚬ (Polled[A] |*| Polled[A]) =
          fork(injectL, injectL)

        val caseValue: (Val[A] |*| Pollable[A]) -⚬ (Polled[A] |*| Polled[A]) =
          id                                             [        Val[A]       |*|          Pollable[A]          ]
            .par(dsl.dup[A], self)                    .to[ (Val[A] |*| Val[A]) |*| (Pollable[A] |*| Pollable[A]) ]
            .>(IXI)                                   .to[ (Val[A] |*| Pollable[A]) |*| (Val[A] |*| Pollable[A]) ]
            .>.fst.injectR[Done].>.snd.injectR[Done]  .to[       Polled[A]          |*|       Polled[A]          ]

        either(caseClosed, caseValue)
      }

      val caseFstClosed: Pollable[A] -⚬ (Done |*| Pollable[A]) =
        introFst > par(done, id)

      val caseFstPolled: Pollable[A] -⚬ (Polled[A] |*| Pollable[A]) =
        id                                           [                  Pollable[A]                       ]
          .>(Pollable.poll[A])                    .to[                   Polled[A]                        ]
          .>(choice(introSnd, dupPolled))         .to[ (Polled[A] |*| One)  |&| (Polled[A] |*| Polled[A]) ]
          .coDistributeL                          .to[  Polled[A] |*| (One  |&|                Polled[A]) ]
          .>.snd.choiceL(done)                    .to[  Polled[A] |*| (Done |&|                Polled[A]) ]
          .>.snd(pack[PollableF[A, *]])           .to[  Polled[A] |*|       Pollable[A]                   ]

      // the case when the first output polls or closes before the second output does
      val caseFst: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) =
        id                                           [                   Pollable[A]                           ]
          .choice(caseFstClosed, caseFstPolled)   .to[ (Done |*| Pollable[A]) |&| (Polled[A]  |*| Pollable[A]) ]
          .coDistributeR                          .to[ (Done                  |&|  Polled[A]) |*| Pollable[A]  ]
          .>.fst(pack[PollableF[A, *]])           .to[              Pollable[A]               |*| Pollable[A]  ]

      // the case when the second output polls or closes before the first output does
      val caseSnd: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) =
        caseFst > swap

      id                                   [          Pollable[A]        ]
        .select(caseFst, caseSnd)       .to[ Pollable[A] |*| Pollable[A] ]
    }

    def dropUntilFirstDemand[A]: Pollable[A] -⚬ Pollable[A] = rec { self =>
        val caseDownstreamRequested: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] = {
          val caseDownstreamClosed: (Val[A] |*| Pollable[A]) -⚬ Done      = join(neglect, Pollable.close)
          val caseDownstreamPulled: (Val[A] |*| Pollable[A]) -⚬ Polled[A] = injectR
          choice(caseDownstreamClosed, caseDownstreamPulled).pack
        }

        val caseNotRequestedYet: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] = {
          id[Val[A] |*| Pollable[A]]
            .>.fst(neglect)
            .>(Pollable.delayBy)
            .>(self)
        }

        val goElem: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] =
          choice(caseDownstreamRequested, caseNotRequestedYet)
            .>(selectSignaledOrNot(LPollable.negativeLPollable))

        id                               [    Pollable[A]                    ]
          .unpack                     .to[ Done |&| Polled[A]                ]
          .chooseR                    .to[ Done |+| (Val[A] |*| Pollable[A]) ]
          .either(empty[A], goElem)   .to[    Pollable[A]                    ]
    }

    def broadcast[A]: Pollable[A] -⚬ PUnlimited[Pollable[A]] = rec { self =>
      val case0: Pollable[A] -⚬ Done                                                  = Pollable.close
      val case1: Pollable[A] -⚬ Pollable[A]                                           = id
      val caseN: Pollable[A] -⚬ (PUnlimited[Pollable[A]] |*| PUnlimited[Pollable[A]]) = dup > par(self, self)

      dropUntilFirstDemand > PUnlimited.create(case0, case1, caseN)
    }

    private[Pollable] type DemandingTree[K, V] = Tree[K, Demanding[V]]
    private[Pollable] object DemandingTree {
      type DT[K, V] = DemandingTree[K, V]
      type NeDT[K, V] = NonEmptyTree[K, Demanding[V]]

      def dispatch[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| DT[K, V]) -⚬ (Done |*| DT[K, V]) =
        Tree.update(Demanding.supply[V].>.left(need > done) > PMaybe.fromEither)
          .>.fst(PMaybe.neglect)

      def dispatchNE[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        NonEmptyTree.update(
          Demanding.supply[V].>.left(need > done) > PMaybe.fromEither,
          ifAbsent = neglect,
        )

      def dispatchNE[A, K: Ordering, V](
        f: Val[A] -⚬ (Val[K] |*| Val[V]),
      ): (Val[A] |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        id                                     [       Val[A]        |*| NeDT[K, V]  ]
          .>.fst(f)                         .to[ (Val[K] |*| Val[V]) |*| NeDT[K, V]  ]
          .>(dispatchNE)                    .to[                  PMaybe[NeDT[K, V]] ]

      def addDemanding[K: Ordering, V]: ((Val[K] |*| Demanding[V]) |*| DT[K, V]) -⚬ DT[K, V] =
        Tree.insertOrUpdate(Demanding.merge)

      def clear[K, V]: DT[K, V] -⚬ Done =
        Tree.clear(Demanding.close > need > done)

      def clearNE[K, V]: NeDT[K, V] -⚬ Done =
        NonEmptyTree.clear(Demanding.close > need > done)

      def addSubscriber[K: Ordering, V]: ((Val[K] |*| Subscriber[V]) |*| DT[K, V]) -⚬ DT[K, V] =
        id                                           [ ( Val[K] |*|       Subscriber[V]                ) |*| DT[K, V] ]
          .>.fst.snd(unpack)                      .to[ ( Val[K] |*| (Need |+|             Demanding[V])) |*| DT[K, V] ]
          .>.fst(distributeL)                    .to[ ((Val[K] |*| Need) |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .>.fst.left.fst(neglect)                .to[ (( Done  |*| Need) |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .>.fst.left(rInvertSignal)              .to[ (        One       |+| (Val[K] |*| Demanding[V])) |*| DT[K, V] ]
          .distributeR
          .either(elimFst, addDemanding)
    }

    opaque type BroadcastByKey[K, V] = LSubscriber[Neg[K] |*| Pollable[V]] |*| Done
    object BroadcastByKey {
      def close[K, V]: BroadcastByKey[K, V] -⚬ Done =
        elimFst(LSubscriber.close > need)

      def subscribe[K, V](k: K): BroadcastByKey[K, V] -⚬ (BroadcastByKey[K, V] |*| Pollable[V]) = {
        val onDemand: LDemanding[Neg[K] |*| Pollable[V]] -⚬ (LSubscriber[Neg[K] |*| Pollable[V]] |*| Pollable[V]) =
          id                                       [          LDemanding[Neg[K] |*| Pollable[V]]                      ]
            .>(LDemanding.exposeDemand)         .to[ (Neg[K] |*| Pollable[V]) |*| LSubscriber[Neg[K] |*| Pollable[V]] ]
            .>.fst(elimFst(constNeg(k) > need)) .to[             Pollable[V]  |*| LSubscriber[Neg[K] |*| Pollable[V]] ]
            .swap                               .to[ LSubscriber[Neg[K] |*| Pollable[V]]     |*|     Pollable[V]      ]

        val onUnsubscribed: Need -⚬ (LSubscriber[Neg[K] |*| Pollable[V]] |*| Pollable[V]) =
          id[Need] > LSubscriber.unsubscribed > introSnd(done > Pollable.empty[V])

        id[ LSubscriber[Neg[K] |*| Pollable[V]] |*| Done ]
          .>.fst(LSubscriber.switch(onDemand, onUnsubscribed))
          .>(IX)
      }
    }

    private def subscribeByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): (Pollable[A] |*| LPollable[Val[K] |*| Subscriber[V]]) -⚬ Done = {
      import Pollable.{DemandingTree => DT}
      import DemandingTree.NeDT
      type KSubs = Val[K] |*| Subscriber[V]

      val discardSubscriber: KSubs -⚬ One =
        par(dsl.neglect[K], Subscriber.close[V]) > rInvertSignal

      val upstreamClosed: (Done |*| (LPolled[KSubs] |*| DT[K, V])) -⚬ Done =
        join(id, join(LPolled.close(discardSubscriber > done), DT.clear))

      def upstreamVal(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Val[A] |*| Pollable[A]) |*| (LPolled[KSubs] |*| DT[K, V])) -⚬ Done =
        id                                   [ (Val[A] |*| Pollable[A]) |*|              (LPolled[KSubs] |*| DT[K, V]) ]
          .>.fst(swap)                    .to[ (Pollable[A] |*| Val[A]) |*|              (LPolled[KSubs] |*| DT[K, V]) ]
          .>(IXI)                         .to[ (Pollable[A] |*| LPolled[KSubs]) |*| (      Val[A]        |*| DT[K, V]) ]
          .>.snd.fst(f)                   .to[ (Pollable[A] |*| LPolled[KSubs]) |*| ((Val[K] |*| Val[V]) |*| DT[K, V]) ]
          .>.snd(DT.dispatch)             .to[ (Pollable[A] |*| LPolled[KSubs]) |*| (Done                |*| DT[K, V]) ]
          .assocRL                        .to[ ((Pollable[A] |*| LPolled[KSubs]) |*| Done)               |*| DT[K, V]  ]
          .>.fst(swap > assocRL)          .to[ ((Done |*| Pollable[A]) |*| LPolled[KSubs])               |*| DT[K, V]  ]
          .>.fst.fst(delayedPoll)         .to[ (  Polled[A]            |*| LPolled[KSubs])               |*| DT[K, V]  ]
          .>(goRec)                       .to[                                                          Done           ]

      def onUpstream(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done =
        assocLR           .to[ Polled[A] |*| (LPolled[KSubs] |*| DT[K, V]) ]
          .distributeR
          .either(upstreamClosed, upstreamVal(goRec))

      val feedToNEDT: (Polled[A] |*| NeDT[K, V]) -⚬ Done =
        LPolled.feedTo(DT.dispatchNE(f)) > join(id, Maybe.neglect(DT.clearNE))

      val forward: (Polled[A] |*| DT[K, V]) -⚬ Done =
        id                                               [  Polled[A] |*| (Done |+|                NeDT[K, V]) ]
          .distributeL                                .to[ (Polled[A] |*| Done) |+| (Polled[A] |*| NeDT[K, V]) ]
          .>.left(join(Polled.close, id))             .to[           Done       |+| (Polled[A] |*| NeDT[K, V]) ]
          .>.right(feedToNEDT)                        .to[           Done       |+|           Done             ]
          .>(either(id, id))                          .to[                     Done                            ]

      val subsClosed: ((Polled[A] |*| Done) |*| DT[K, V]) -⚬ Done =
        id                             [ (Polled[A] |*| Done) |*| DT[K, V] ]
          .>(IX)                    .to[ (Polled[A] |*| DT[K, V]) |*| Done ]
          .>.fst(forward)           .to[           Done           |*| Done ]
          .>(join)                  .to[                         Done      ]

      def newSubscriber(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| (KSubs |*| LPollable[KSubs])) |*| DT[K, V]) -⚬ Done =
        id                                 [ ( Polled[A] |*| (KSubs  |*|  LPollable[KSubs])) |*| DT[K, V]  ]
          .>.fst.snd(swap)              .to[ ( Polled[A] |*| (LPollable[KSubs]  |*|  KSubs)) |*| DT[K, V]  ]
          .>.fst.assocRL                .to[ ((Polled[A] |*|  LPollable[KSubs]) |*|  KSubs ) |*| DT[K, V]  ]
          .assocLR                      .to[  (Polled[A] |*|  LPollable[KSubs]) |*| (KSubs   |*| DT[K, V]) ]
          .>.snd(DT.addSubscriber)      .to[  (Polled[A] |*|  LPollable[KSubs]) |*|              DT[K, V]  ]
          .>.fst.snd(LPollable.poll)    .to[  (Polled[A] |*|    LPolled[KSubs]) |*|              DT[K, V]  ]
          .>(goRec)                     .to[                                   Done                        ]

      def onSubs(
        goRec: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done =
        id[ (Polled[A] |*| LPolled[KSubs]) |*| DT[K, V] ]
          .>.fst(distributeL)
          .distributeR
          .either(subsClosed, newSubscriber(goRec))

      val go: ((Polled[A] |*| LPolled[KSubs]) |*| DT[K, V]) -⚬ Done = rec { self =>
        import LPolled.positiveLPolled

        implicit def positiveKSubs: SignalingJunction.Positive[KSubs] =
          SignalingJunction.Positive.byFst[Val[K], Subscriber[V]]

        id                                           [ (Polled[A] |*| LPolled[KSubs]) |*| DT[K, V] ]
          .>.fst(lib.race)
          .distributeR
          .either(onUpstream(self), onSubs(self)) .to[                               Done          ]
      }

      id[Pollable[A] |*| LPollable[KSubs]]
        .>(par(poll, LPollable.poll))
        .introSnd(done > Tree.empty[K, Demanding[V]])
        .>(go)
    }

    def broadcastByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): Pollable[A] -⚬ BroadcastByKey[K, V] = {
      val lInvert: One -⚬ (LPollable[Val[K] |*| Subscriber[V]] |*| LSubscriber[Neg[K] |*| Pollable[V]]) =
        subscriberPollableDuality.lInvert

      id                                [  Pollable[A]                                                                                  ]
        .introSnd(lInvert).assocRL   .to[ (Pollable[A] |*| LPollable[Val[K] |*| Subscriber[V]]) |*| LSubscriber[Neg[K] |*| Pollable[V]] ]
        .>.fst(subscribeByKey(f))    .to[             Done                                      |*| LSubscriber[Neg[K] |*| Pollable[V]] ]
        .swap                        .to[                                        BroadcastByKey[K, V]                                   ]
    }
  }

  object Polled {
    def close[A]: Polled[A] -⚬ Done =
      LPolled.close(dsl.neglect[A])

    def empty[A]: Done -⚬ Polled[A] =
      LPolled.empty

    def cons[A]: (Val[A] |*| Pollable[A]) -⚬ Polled[A] =
      LPolled.cons

    def unpoll[A]: Polled[A] -⚬ Pollable[A] =
      LPolled.unpoll[Val[A]]

    def delayBy[A]: (Done |*| Polled[A]) -⚬ Polled[A] =
      LPolled.delayBy

    implicit def positivePolled[A]: SignalingJunction.Positive[Polled[A]] =
      LPolled.positiveLPolled[Val[A]]

    /** Merges two [[Polled]]s into one.
      * Left-biased: whenever there is a value available from both upstreams, favors the first one.
      *
      * @param mergePollables left-biased merge of two [[Pollable]]s.
      */
    def merge[A](
      mergePollables: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A],
    ): (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
      LPolled.merge(mergePollables)
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
        id                                               [  Demanding[A] |*|       Subscriber[A]                       ]
          .>.snd(unpack)                              .to[  Demanding[A] |*| (Need |+|                   Demanding[A]) ]
          .distributeL                                .to[ (Demanding[A] |*| Need) |+| (Demanding[A] |*| Demanding[A]) ]
          .>(either(elimSnd(need), mergeDemandings))  .to[                     Demanding[A]                            ]
          .injectR[Need].pack[SubscriberF[A, *]]      .to[                    Subscriber[A]                            ]

      val caseFstReady: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        id                                     [       Subscriber[A]                         |*| Subscriber[A]  ]
          .>.fst(unpack)                    .to[ (Need |+|                     Demanding[A]) |*| Subscriber[A]  ]
          .distributeR                      .to[ (Need |*| Subscriber[A]) |+| (Demanding[A]  |*| Subscriber[A]) ]
          .either(fstClosed, fstDemanding)  .to[                     Subscriber[A]                              ]

      val caseSndReady: (Subscriber[A] |*| Subscriber[A]) -⚬ Subscriber[A] =
        swap > caseFstReady

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
          .>(par(chooseR, chooseR))                 .to[ (Neg[A] |*| Subscriber[A]) |*| (Neg[A] |*| Subscriber[A]) ]
          .>(IXI)                                   .to[ (Neg[A] |*| Neg[A]) |*| (Subscriber[A] |*| Subscriber[A]) ]
          .par(mergeDemands[A], mergeSubscribers)   .to[        Neg[A]       |*|            Subscriber[A]          ]

      choice(caseClosed, caseDemanding)
    }

    def merge[A]: (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A] = rec { self =>
      merge(Subscriber.merge(self))
    }

    implicit def negativeDemanding[A]: SignalingJunction.Negative[Demanding[A]] =
      LDemanding.negativeLDemanding[Neg[A]]
  }

  def rInvertSubscriber[A]: (Subscriber[A] |*| Pollable[A]) -⚬ One =
    rInvertLSubscriber(fulfill)

  def lInvertPollable[A]: One -⚬ (Pollable[A] |*| Subscriber[A]) =
    lInvertLPollable(promise)

  def rInvertProducingF[A, x, y](rInvertSub: (x |*| y) -⚬ One): (ProducingF[A, x] |*| ConsumerF[A, y]) -⚬ One =
    rInvertEither(
      rInvertSignal,
      swap > rInvertEither(
        swap > rInvertSignal,
        rInvertPair(
          swap > fulfill[A],
          swap > rInvertSub
        )
      )
    )

  def lInvertConsumerF[A, x, y](lInvertSub: One -⚬ (y |*| x)): One -⚬ (ConsumerF[A, y] |*| ProducingF[A, x]) =
    lInvertChoice(
      lInvertSignal,
      lInvertChoice(
        lInvertSignal > swap,
        lInvertPair(
          promise[A] > swap,
          lInvertSub > swap
        )
      ) > swap
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
      .>.snd(unpack)               .to[ Pollable[A] |*| (Need   |+|                      (Need |&| (Neg[B] |*| Subscriber[B])))]
      .distributeL                 .to[(Pollable[A] |*|  Need)  |+|   (Pollable[A]   |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .>.left.fst(Pollable.close)  .to[(Done        |*|  Need)  |+|   (Pollable[A]   |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .>.left(rInvertSignal)       .to[ One |+| (                      Pollable[A]   |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .>.right.fst(Pollable.poll)  .to[ One |+| ((Done |+| (Val[A] |*| Pollable[A])) |*| (Need |&| (Neg[B] |*| Subscriber[B])))]
      .>.right(matchingChoiceLR)   .to[ One |+| ((Done |*| Need) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])))]
      .>.right.left(rInvertSignal) .to[ One |+| (      One       |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])))]
      .assocRL                     .to[(One |+|        One     ) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]
      .>.left(either(id, id))      .to[     One                  |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Subscriber[B])) ]
}
