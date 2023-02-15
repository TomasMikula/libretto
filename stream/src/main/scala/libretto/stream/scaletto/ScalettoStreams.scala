package libretto.stream.scaletto

import libretto.CoreLib
import libretto.lambda.util.SourcePos
import libretto.scaletto.{Scaletto, ScalettoLib}
import libretto.stream.InvertStreams
import scala.annotation.{tailrec, targetName}
import scala.concurrent.duration.FiniteDuration

object ScalettoStreams {
  type Of[
    DSL <: Scaletto,
    Lib <: CoreLib[DSL],
    SLib <: ScalettoLib[DSL, Lib],
    Streams <: InvertStreams[DSL, Lib],
  ] = ScalettoStreams {
    type Dsl           = DSL
    type CoreLib       = Lib
    type ScalettoLib   = SLib
    type InvertStreams = Streams
  }

  def apply(
    scaletto: Scaletto,
    lib: CoreLib[scaletto.type],
    sLib: ScalettoLib[scaletto.type, lib.type],
    iStreams: InvertStreams[scaletto.type, lib.type],
  )
  : ScalettoStreams.Of[scaletto.type, lib.type, sLib.type, iStreams.type] =
    new ScalettoStreams {
      override type Dsl           = scaletto.type
      override type CoreLib       = lib.type
      override type ScalettoLib   = sLib.type
      override type InvertStreams = iStreams.type

      override val dsl           = scaletto
      override val coreLib       = lib
      override val scalettoLib   = sLib
      override val invertStreams = iStreams
    }
}

abstract class ScalettoStreams {
  type Dsl           <: Scaletto
  type CoreLib       <: libretto.CoreLib[Dsl]
  type ScalettoLib   <: libretto.scaletto.ScalettoLib[Dsl, CoreLib]
  type InvertStreams <: libretto.stream.InvertStreams[Dsl, CoreLib]

  val dsl: Dsl
  val coreLib: CoreLib & libretto.CoreLib[dsl.type]
  val scalettoLib: ScalettoLib & libretto.scaletto.ScalettoLib[dsl.type, coreLib.type]
  val invertStreams: InvertStreams & libretto.stream.InvertStreams[dsl.type, coreLib.type]

  private lazy val Tree = BinarySearchTree(dsl, coreLib, scalettoLib)

  import dsl._
  import dsl.$._
  import coreLib._
  import scalettoLib._
  import invertStreams._
  import Tree._

  type PollableF[A, X] = StreamFollowerF[Done, Val[A], X]
  type Pollable[A] = LPollable[Val[A]]
  type Polled[A] = LPolled[Val[A]]

  type ValueDrain[A] = Drain[Val[A]]

  @deprecated
  type ProducingF[A, X]  = Done |+| (Done |&| (Val[A] |*| X))
  @deprecated
  type Producing[A] = Rec[ProducingF[A, *]]

  @deprecated
  type ConsumerF[A, X] = Need |&| (Need |+| (Neg[A] |*| X))
  @deprecated
  type Consumer[A] = Rec[ConsumerF[A, *]]

  object Pollable {
    def from[Z, A](
      onClose: Z -⚬ Done,
      onPoll: Z -⚬ (Done |+| (Val[A] |*| Pollable[A]))
    ): Z -⚬ Pollable[A] =
      LPollable.from(onClose, onPoll)

    def fromChoice[A]: (Done |&| Polled[A]) -⚬ Pollable[A] =
      LPollable.pack[Val[A]]

    def close[A]: Pollable[A] -⚬ Done =
      LPollable.close[Val[A]]

    def poll[A]: Pollable[A] -⚬ Polled[A] =
      LPollable.poll[Val[A]]

    def delayedPoll[A]: (Done |*| Pollable[A]) -⚬ Polled[A] =
      LPollable.delayedPoll[Val[A]]

    /** Polls and discards all elements. */
    def drain[A]: Pollable[A] -⚬ Done =
      LPollable.drain[Val[A]]

    def empty[A]: Done -⚬ Pollable[A] =
      LPollable.empty[Val[A]]

    def cons[A]: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] =
      LPollable.cons

    def fromLList[A]: LList[Val[A]] -⚬ Pollable[A] =
      LPollable.fromLList[Val[A]]

    def detain[A]: Pollable[A] -⚬ Detained[Pollable[A]] =
      LPollable.detain[Val[A]]

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

    def fromList[A](as: List[A]): Done -⚬ Pollable[A] = {
      @tailrec def go(ras: List[A], acc: Done -⚬ Pollable[A]): Done -⚬ Pollable[A] =
        ras match {
          case head :: tail => go(tail, forkMap(constVal(head), acc) > Pollable.cons)
          case Nil          => acc
        }

      go(as.reverse, Pollable.empty[A])
    }

    def of[A](as: A*): Done -⚬ Pollable[A] =
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
        joinMap(neglect, Pollable.close)

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
          joinMap(neglect, Pollable.close)

        val poll:(Val[S] |*| Pollable[A]) -⚬ (Done |+| (Val[B] |*| Pollable[B])) =
          id[Val[S] |*| Pollable[A]]          .to[ Val[S] |*|                                    Pollable[A]   ]
            .>.snd(Pollable.poll)             .to[ Val[S] |*| (Done  |+|             (Val[A] |*| Pollable[A])) ]
            .distributeL                      .to[ (Val[S] |*| Done) |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .>.left(joinMap(neglect, id))     .to[        Done       |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
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
          forkMap(injectL, injectL)

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
          val caseDownstreamClosed: (Val[A] |*| Pollable[A]) -⚬ Done      = joinMap(neglect, Pollable.close)
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

    private[Pollable] type DemandingTree[K, V] = Tree[K, ValueDrain.Pulling[V]]
    private[Pollable] object DemandingTree {
      type DT[K, V] = DemandingTree[K, V]
      type NeDT[K, V] = NonEmptyTree[K, ValueDrain.Pulling[V]]

      def dispatch[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| DT[K, V]) -⚬ (Done |*| DT[K, V]) =
        Tree.update(ValueDrain.Pulling.supply[V].>.left(need > done) > PMaybe.fromEither)
          .>.fst(PMaybe.neglect)

      def dispatchNE[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        NonEmptyTree.update(
          ValueDrain.Pulling.supply[V].>.left(need > done) > PMaybe.fromEither,
          ifAbsent = neglect,
        )

      def dispatchNE[A, K: Ordering, V](
        f: Val[A] -⚬ (Val[K] |*| Val[V]),
      ): (Val[A] |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        id                                     [       Val[A]        |*| NeDT[K, V]  ]
          .>.fst(f)                         .to[ (Val[K] |*| Val[V]) |*| NeDT[K, V]  ]
          .>(dispatchNE)                    .to[                  PMaybe[NeDT[K, V]] ]

      def addPulling[K, V](using Ordering[K]): ((Val[K] |*| ValueDrain.Pulling[V]) |*| DT[K, V]) -⚬ DT[K, V] =
        Tree.insertOrUpdate(ValueDrain.Pulling.merge)

      def clear[K, V]: DT[K, V] -⚬ Done =
        Tree.clear(ValueDrain.Pulling.close > need > done)

      def clearNE[K, V]: NeDT[K, V] -⚬ Done =
        NonEmptyTree.clear(ValueDrain.Pulling.close > need > done)

      def addSubscriber[K: Ordering, V]: ((Val[K] |*| -[Pollable[V]]) |*| DT[K, V]) -⚬ DT[K, V] =
        λ { case ((k |*| out) |*| tree) =>
          val drain: $[ValueDrain[V]] =
            ValueDrain.fromInvertedSource(out)
          drain.toEither switch {
            case Left(closing)  => tree alsoElim rInvertSignal(neglect(k) |*| closing)
            case Right(pulling) => addPulling((k |*| pulling) |*| tree)
          }
        }
    }

    opaque type BroadcastByKey[K, V] = Drain[Val[K] |*| -[Pollable[V]]] |*| Done
    object BroadcastByKey {
      def close[K, V]: BroadcastByKey[K, V] -⚬ Done =
        elimFst(Drain.close > need)

      def subscribe[K, V](k: K): BroadcastByKey[K, V] -⚬ (BroadcastByKey[K, V] |*| Pollable[V]) = {
        val onDemand: Drain.Pulling[Val[K] |*| -[Pollable[V]]] -⚬ (Drain[Val[K] |*| -[Pollable[V]]] |*| Pollable[V]) =
          id                                       [           Drain.Pulling[Val[K] |*| -[Pollable[V]]]                    ]
            .>(Drain.Pulling.warrant)           .to[ -[Val[K]  |*|   -[Pollable[V]]]  |*| Drain[Val[K] |*| -[Pollable[V]]] ]
            .>.fst(distributeInversion)         .to[ -[Val[K]] |*| -[-[Pollable[V]]]  |*| Drain[Val[K] |*| -[Pollable[V]]] ]
            .>.fst(elimFst(constNeg(k) > need)) .to[               -[-[Pollable[V]]]  |*| Drain[Val[K] |*| -[Pollable[V]]] ]
            .>.fst(die)                         .to[                   Pollable[V]    |*| Drain[Val[K] |*| -[Pollable[V]]] ]
            .swap                               .to[ Drain[Val[K] |*| -[Pollable[V]]] |*|           Pollable[V]           ]

        val onUnsubscribed: Need -⚬ (Drain[Val[K] |*| -[Pollable[V]]] |*| Pollable[V]) =
          id[Need] > Drain.closed > introSnd(done > Pollable.empty[V])

        id[ Drain[Val[K] |*| -[Pollable[V]]] |*| Done ]
          .>.fst(Drain.switch(onUnsubscribed, onDemand))
          .>(IX)
      }
    }

    private def subscribeByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): (Pollable[A] |*| LPollable[Val[K] |*| -[Pollable[V]]]) -⚬ Done = {
      import Pollable.{DemandingTree => DT}
      import DemandingTree.NeDT
      type KSubs = Val[K] |*| -[Pollable[V]]

      val discardSubscriber: KSubs -⚬ One =
        λ { case (k |*| out) => (k > dsl.neglect > Pollable.empty[V]) supplyTo out }

      val upstreamClosed: (Done |*| (LPolled[KSubs] |*| DT[K, V])) -⚬ Done =
        joinMap(id, joinMap(LPolled.close(discardSubscriber > done), DT.clear))

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
        LPolled.feedTo(DT.dispatchNE(f)) > joinMap(id, Maybe.neglect(DT.clearNE))

      val forward: (Polled[A] |*| DT[K, V]) -⚬ Done =
        id                                               [  Polled[A] |*| (Done |+|                NeDT[K, V]) ]
          .distributeL                                .to[ (Polled[A] |*| Done) |+| (Polled[A] |*| NeDT[K, V]) ]
          .>.left(joinMap(Polled.close, id))          .to[           Done       |+| (Polled[A] |*| NeDT[K, V]) ]
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
          SignalingJunction.Positive.byFst[Val[K], -[Pollable[V]]]

        id                                           [ (Polled[A] |*| LPolled[KSubs]) |*| DT[K, V] ]
          .>.fst(lib.race)
          .distributeR
          .either(onUpstream(self), onSubs(self)) .to[                               Done          ]
      }

      id[Pollable[A] |*| LPollable[KSubs]]
        .>(par(poll, LPollable.poll))
        .introSnd(done > Tree.empty[K, ValueDrain.Pulling[V]])
        .>(go)
    }

    def broadcastByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): Pollable[A] -⚬ BroadcastByKey[K, V] = {
      val lInvert: One -⚬ (LPollable[Val[K] |*| -[Pollable[V]]] |*| Drain[Val[K] |*| -[Pollable[V]]]) =
        lInvertSource

      id                                [  Pollable[A]                                                                                ]
        .introSnd(lInvert).assocRL   .to[ (Pollable[A] |*| LPollable[Val[K] |*| -[Pollable[V]]]) |*| Drain[Val[K] |*| -[Pollable[V]]] ]
        .>.fst(subscribeByKey(f))    .to[             Done                                       |*| Drain[Val[K] |*| -[Pollable[V]]] ]
        .swap                        .to[                                         BroadcastByKey[K, V]                                ]
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

  object ValueDrain {
    type Pulling[A] = Drain.Pulling[Val[A]]

    def close[A]: ValueDrain[A] -⚬ Need =
      LSubscriber.close

    def toEither[A]: ValueDrain[A] -⚬ (Need |+| Pulling[A]) =
      Drain.toEither[Val[A]]

    def fromInvertedSource[A]: -[Pollable[A]] -⚬ ValueDrain[A] =
      λ { invSrc => invSrc unInvertWith (lInvertSource > swap) }

    implicit def positiveValueDrain[A]: SignalingJunction.Positive[ValueDrain[A]] =
      LSubscriber.positiveLSubscriber[Neg[A]]

    type Demanding[A] = ValueDrain.Pulling[A]
    private[ScalettoStreams] def merge[A](
      mergeDemandings: (Demanding[A] |*| Demanding[A]) -⚬ Demanding[A]
    ): (ValueDrain[A] |*| ValueDrain[A]) -⚬ ValueDrain[A] = {
      val fstClosed: (Need |*| ValueDrain[A]) -⚬ ValueDrain[A] =
        elimFst(need)

      val fstDemanding: (Demanding[A] |*| ValueDrain[A]) -⚬ ValueDrain[A] =
        id                                               [  Demanding[A] |*|       ValueDrain[A]                       ]
          .>.snd(unpack)                              .to[  Demanding[A] |*| (Need |+|                   Demanding[A]) ]
          .distributeL                                .to[ (Demanding[A] |*| Need) |+| (Demanding[A] |*| Demanding[A]) ]
          .>(either(elimSnd(need), mergeDemandings))  .to[                     Demanding[A]                            ]
          .>(LSubscriber.demanding)                   .to[                    ValueDrain[A]                            ]

      val caseFstReady: (ValueDrain[A] |*| ValueDrain[A]) -⚬ ValueDrain[A] =
        id                                     [       ValueDrain[A]                         |*| ValueDrain[A]  ]
          .>.fst(unpack)                    .to[ (Need |+|                     Demanding[A]) |*| ValueDrain[A]  ]
          .distributeR                      .to[ (Need |*| ValueDrain[A]) |+| (Demanding[A]  |*| ValueDrain[A]) ]
          .either(fstClosed, fstDemanding)  .to[                     ValueDrain[A]                              ]

      val caseSndReady: (ValueDrain[A] |*| ValueDrain[A]) -⚬ ValueDrain[A] =
        swap > caseFstReady

      id                                         [ ValueDrain[A] |*| ValueDrain[A] ]
        .race(caseFstReady, caseSndReady)     .to[           ValueDrain[A]         ]
    }

    def merge[A]: (ValueDrain[A] |*| ValueDrain[A]) -⚬ ValueDrain[A] = rec { self =>
      merge(ValueDrain.Pulling.merge(self))
    }

    object Pulling {
      def close[A]: Pulling[A] -⚬ Need =
        chooseL

      def supply[A]: (Val[A] |*| Pulling[A]) -⚬ (Need |+| Pulling[A]) =
        LDemanding.supply(fulfill[A])

      private[ScalettoStreams] def merge[A](
        mergeDrains: (ValueDrain[A] |*| ValueDrain[A]) -⚬ ValueDrain[A]
      ): (Pulling[A] |*| Pulling[A]) -⚬ Pulling[A] = {
        val caseClosed: (Pulling[A] |*| Pulling[A]) -⚬ Need =
          forkMapNeed(chooseL, chooseL)

        val caseDemanding: (Pulling[A] |*| Pulling[A]) -⚬ (Neg[A] |*| ValueDrain[A]) =
          id                                        [      Pulling[A]            |*|      Pulling[A]            ]
            .>(par(chooseR, chooseR))            .to[ (Neg[A] |*| ValueDrain[A]) |*| (Neg[A] |*| ValueDrain[A]) ]
            .>(IXI)                              .to[ (Neg[A] |*| Neg[A]) |*| (ValueDrain[A] |*| ValueDrain[A]) ]
            .par(mergeDemands[A], mergeDrains)   .to[        Neg[A]       |*|            ValueDrain[A]          ]

        choice(caseClosed, caseDemanding)
      }

      def merge[A]: (Pulling[A] |*| Pulling[A]) -⚬ Pulling[A] = rec { self =>
        merge(ValueDrain.merge(self))
      }
    }
  }

  extension [A](drain: $[ValueDrain[A]]) {
    @targetName("valueDrainToEither")
    def toEither(using SourcePos, LambdaContext): $[Need |+| ValueDrain.Pulling[A]] =
      drain > ValueDrain.toEither
  }

  def rInvertValueDrain[A]: (ValueDrain[A] |*| Pollable[A]) -⚬ One =
    rInvertLSubscriber(swap > fulfill)

  def lInvertPollable[A]: One -⚬ (Pollable[A] |*| ValueDrain[A]) =
    lInvertLPollable(promise > swap)

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

  /** If either the source or the drain is completed, complete the other one and be done.
    * Otherwise, expose their offer and demand, respectively.
    */
  def relayCompletion[A, B]: (Pollable[A] |*| ValueDrain[B]) -⚬ (One |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| ValueDrain[B]))) =
    id                                [ Pollable[A] |*| (                   ValueDrain[B]                                     )]
      .>.snd(unpack)               .to[ Pollable[A] |*| (Need   |+|                      (Need |&| (Neg[B] |*| ValueDrain[B])))]
      .distributeL                 .to[(Pollable[A] |*|  Need)  |+|   (Pollable[A]   |*| (Need |&| (Neg[B] |*| ValueDrain[B])))]
      .>.left.fst(Pollable.close)  .to[(Done        |*|  Need)  |+|   (Pollable[A]   |*| (Need |&| (Neg[B] |*| ValueDrain[B])))]
      .>.left(rInvertSignal)       .to[ One |+| (                      Pollable[A]   |*| (Need |&| (Neg[B] |*| ValueDrain[B])))]
      .>.right.fst(Pollable.poll)  .to[ One |+| ((Done |+| (Val[A] |*| Pollable[A])) |*| (Need |&| (Neg[B] |*| ValueDrain[B])))]
      .>.right(matchingChoiceLR)   .to[ One |+| ((Done |*| Need) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| ValueDrain[B])))]
      .>.right.left(rInvertSignal) .to[ One |+| (      One       |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| ValueDrain[B])))]
      .assocRL                     .to[(One |+|        One     ) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| ValueDrain[B])) ]
      .>.left(either(id, id))      .to[     One                  |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| ValueDrain[B])) ]
}
