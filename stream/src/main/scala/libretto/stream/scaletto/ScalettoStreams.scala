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

  type ValSource[A] = Source[Val[A]]

  type ValDrain[A] = Drain[Val[A]]

  @deprecated
  type ProducingF[A, X]  = Done |+| (Done |&| (Val[A] |*| X))
  @deprecated
  type Producing[A] = Rec[ProducingF[A, *]]

  @deprecated
  type ConsumerF[A, X] = Need |&| (Need |+| (Neg[A] |*| X))
  @deprecated
  type Consumer[A] = Rec[ConsumerF[A, *]]

  object ValSource {
    type Polled[A] = Source.Polled[Val[A]]

    def from[Z, A](
      onClose: Z -⚬ Done,
      onPoll: Z -⚬ (Done |+| (Val[A] |*| ValSource[A]))
    ): Z -⚬ ValSource[A] =
      Source.from(onClose, onPoll)

    def fromChoice[A]: (Done |&| Polled[A]) -⚬ ValSource[A] =
      Source.pack[Val[A]]

    def toChoice[A]: ValSource[A] -⚬ (Done |&| Polled[A]) =
      Source.unpack[Val[A]]

    def close[A]: ValSource[A] -⚬ Done =
      Source.close[Val[A]]

    def poll[A]: ValSource[A] -⚬ Polled[A] =
      Source.poll[Val[A]]

    def delayedPoll[A]: (Done |*| ValSource[A]) -⚬ Polled[A] =
      Source.delayedPoll[Val[A]]

    /** Polls and discards all elements. */
    def drain[A]: ValSource[A] -⚬ Done =
      Source.drain[Val[A]]

    def empty[A]: Done -⚬ ValSource[A] =
      Source.empty[Val[A]]

    def cons[A]: (Val[A] |*| ValSource[A]) -⚬ ValSource[A] =
      Source.cons

    def fromLList[A]: LList[Val[A]] -⚬ ValSource[A] =
      Source.fromLList[Val[A]]

    def detain[A]: ValSource[A] -⚬ Detained[ValSource[A]] =
      Source.detain[Val[A]]

    def delayBy[A]: (Done |*| ValSource[A]) -⚬ ValSource[A] =
      Source.delayBy[Val[A]]

    def delayable[A]: ValSource[A] -⚬ (Need |*| ValSource[A]) =
      Source.delayable[Val[A]]

    def notifyAction[A]: (Pong |*| ValSource[A]) -⚬ ValSource[A] =
      snd(toChoice) > notifyChoice > fromChoice

    def delay[A](d: FiniteDuration): ValSource[A] -⚬ ValSource[A] = {
      id                                           [          ValSource[A] ]
        .<(notifyAction)                      .from[ Pong |*| ValSource[A] ]
        .<.fst(strengthenPong)                .from[ Need |*| ValSource[A] ]
        .<.fst(delayNeed(d))                  .from[ Need |*| ValSource[A] ]
        .<(delayable)                         .from[          ValSource[A] ]
    }

    def fromList[A]: Val[List[A]] -⚬ ValSource[A] = rec { self =>
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

      ValSource.from(close, poll)
    }

    def fromList[A](as: List[A]): Done -⚬ ValSource[A] = {
      @tailrec def go(ras: List[A], acc: Done -⚬ ValSource[A]): Done -⚬ ValSource[A] =
        ras match {
          case head :: tail => go(tail, forkMap(constVal(head), acc) > ValSource.cons)
          case Nil          => acc
        }

      go(as.reverse, ValSource.empty[A])
    }

    def of[A](as: A*): Done -⚬ ValSource[A] =
      fromList(as.toList)

    def toList[A]: ValSource[A] -⚬ Val[List[A]] = {
      def go: (ValSource[A] |*| Val[List[A]]) -⚬ Val[List[A]] = rec { self =>
        id                                   [                        ValSource[A]                    |*| Val[List[A]]  ]
          .>.fst(poll)                    .to[ (Done                   |+| (Val[A] |*| ValSource[A])) |*| Val[List[A]]  ]
          .distributeR                    .to[ (Done |*| Val[List[A]]) |+| ((Val[A] |*| ValSource[A]) |*| Val[List[A]]) ]
          .>.left.snd(mapVal(_.reverse))  .to[ (Done |*| Val[List[A]]) |+| ((Val[A] |*| ValSource[A]) |*| Val[List[A]]) ]
          .>.left.awaitFst                .to[           Val[List[A]]  |+| ((Val[A] |*| ValSource[A]) |*| Val[List[A]]) ]
          .>.right.fst(swap)              .to[           Val[List[A]]  |+| ((ValSource[A] |*| Val[A]) |*| Val[List[A]]) ]
          .>.right.assocLR                .to[           Val[List[A]]  |+| (ValSource[A] |*| (Val[A] |*| Val[List[A]])) ]
          .>.right.snd(unliftPair)        .to[           Val[List[A]]  |+| (ValSource[A] |*|    Val[(A, List[A])]     ) ]
          .>.right.snd(mapVal(_ :: _))    .to[           Val[List[A]]  |+| (ValSource[A] |*|      Val[List[A]]        ) ]
          .>.right(self)                  .to[           Val[List[A]]  |+|           Val[List[A]]                       ]
          .either(id, id)                 .to[                     Val[List[A]]                                         ]
      }

      id[ValSource[A]]
        .>(introSnd(const(List.empty[A])))
        .>(go)
    }

    def repeatedly[A](f: Done -⚬ Val[A]): Done -⚬ ValSource[A] =
      Source.repeatedly[Val[A]](f)

    def map[A, B](f: A => B): ValSource[A] -⚬ ValSource[B] = {
      val g: Val[A] -⚬ Val[B] = mapVal(f)
      Source.map(g)
    }

    def forEachSequentially[A](f: Val[A] -⚬ Done): ValSource[A] -⚬ Done =
      Source.forEachSequentially[Val[A]](f)

    def prepend[A]: (Val[A] |*| ValSource[A]) -⚬ ValSource[A] = {
      val close: (Val[A] |*| ValSource[A]) -⚬ Done =
        joinMap(neglect, ValSource.close)

      val poll: (Val[A] |*| ValSource[A]) -⚬ Polled[A] =
        injectR

      ValSource.from(close, poll)
    }

    def concat[A]: (ValSource[A] |*| ValSource[A]) -⚬ ValSource[A] =
      Source.concat

    def statefulMap[S, A, B](f: ((S, A)) => (S, B))(initialState: S): ValSource[A] -⚬ ValSource[B] = {
      val ff: (Val[S] |*| Val[A]) -⚬ (Val[S] |*| Val[B]) =
        unliftPair[S, A]
          .>(mapVal(f))
          .>(liftPair[S, B])

      val inner: (Val[S] |*| ValSource[A]) -⚬ ValSource[B] = rec { self =>
        val close: (Val[S] |*| ValSource[A]) -⚬ Done =
          joinMap(neglect, ValSource.close)

        val poll:(Val[S] |*| ValSource[A]) -⚬ (Done |+| (Val[B] |*| ValSource[B])) =
          id[Val[S] |*| ValSource[A]]         .to[ Val[S] |*|                                    ValSource[A]   ]
            .>.snd(ValSource.poll)            .to[ Val[S] |*| (Done  |+|             (Val[A] |*| ValSource[A])) ]
            .distributeL                      .to[ (Val[S] |*| Done) |+| (Val[S] |*| (Val[A] |*| ValSource[A])) ]
            .>.left(joinMap(neglect, id))     .to[        Done       |+| (Val[S] |*| (Val[A] |*| ValSource[A])) ]
            .>.right.assocRL                  .to[        Done       |+| ((Val[S] |*| Val[A]) |*| ValSource[A]) ]
            .>.right.fst(ff)                  .to[        Done       |+| ((Val[S] |*| Val[B]) |*| ValSource[A]) ]
            .>.right.fst(swap)                .to[        Done       |+| ((Val[B] |*| Val[S]) |*| ValSource[A]) ]
            .>.right.assocLR                  .to[        Done       |+| (Val[B] |*| (Val[S] |*| ValSource[A])) ]
            .>.right.snd(self)                .to[        Done       |+| (Val[B] |*|     ValSource[B]         ) ]

        ValSource.from(close, poll)
      }

      id[ValSource[A]]                  .to[            ValSource[A] ]
        .introFst(const(initialState))  .to[ Val[S] |*| ValSource[A] ]
        .>(inner)                       .to[     ValSource[B]        ]
    }

    /** Splits a stream of "`A` or `B`" to a stream of `A` and a stream of `B`.
      *
      * Polls the upstream only after ''both'' downstreams poll.
      * When either of the downstreams closes, the other downstream and the upstream are closed as well.
      */
    def partition[A, B]: ValSource[Either[A, B]] -⚬ (ValSource[A] |*| ValSource[B]) =
      Source.map(liftEither[A, B]) > Source.partition

    /** Merges two [[ValSource]]s into one.
      * Left-biased: when there is a value available from both upstreams, favors the first one.
      */
    def merge[A]: (ValSource[A] |*| ValSource[A]) -⚬ ValSource[A] =
      Source.merge[Val[A]]

    /** Merges a list of [[ValSource]]s into a single [[ValSource]].
      * Head-biased: when there is an element available from multiple upstreams, favors the upstream closest to the
      * head of the input list.
      */
    def mergeAll[A]: LList[ValSource[A]] -⚬ ValSource[A] =
      Source.mergeAll[Val[A]]

    def dup[A]: ValSource[A] -⚬ (ValSource[A] |*| ValSource[A]) = rec { self =>
      val dupPolled: Polled[A] -⚬ (Polled[A] |*| Polled[A]) = {
        val caseClosed: Done -⚬ (Polled[A] |*| Polled[A]) =
          forkMap(injectL, injectL)

        val caseValue: (Val[A] |*| ValSource[A]) -⚬ (Polled[A] |*| Polled[A]) =
          id                                             [        Val[A]       |*|          ValSource[A]           ]
            .par(dsl.dup[A], self)                    .to[ (Val[A] |*| Val[A]) |*| (ValSource[A] |*| ValSource[A]) ]
            .>(IXI)                                   .to[ (Val[A] |*| ValSource[A]) |*| (Val[A] |*| ValSource[A]) ]
            .>.fst.injectR[Done].>.snd.injectR[Done]  .to[       Polled[A]           |*|       Polled[A]           ]

        either(caseClosed, caseValue)
      }

      val caseFstClosed: ValSource[A] -⚬ (Done |*| ValSource[A]) =
        introFst > par(done, id)

      val caseFstPolled: ValSource[A] -⚬ (Polled[A] |*| ValSource[A]) =
        id                                           [                 ValSource[A]                       ]
          .>(ValSource.poll[A])                   .to[                   Polled[A]                        ]
          .>(choice(introSnd, dupPolled))         .to[ (Polled[A] |*| One)  |&| (Polled[A] |*| Polled[A]) ]
          .coDistributeL                          .to[  Polled[A] |*| (One  |&|                Polled[A]) ]
          .>.snd.choiceL(done)                    .to[  Polled[A] |*| (Done |&|                Polled[A]) ]
          .>.snd(ValSource.fromChoice)            .to[  Polled[A] |*|       ValSource[A]                   ]

      // the case when the first output polls or closes before the second output does
      val caseFst: ValSource[A] -⚬ (ValSource[A] |*| ValSource[A]) =
        id                                           [                   ValSource[A]                            ]
          .choice(caseFstClosed, caseFstPolled)   .to[ (Done |*| ValSource[A]) |&| (Polled[A]  |*| ValSource[A]) ]
          .coDistributeR                          .to[ (Done                   |&|  Polled[A]) |*| ValSource[A]  ]
          .>.fst(ValSource.fromChoice)            .to[                 ValSource[A]            |*| ValSource[A]  ]

      // the case when the second output polls or closes before the first output does
      val caseSnd: ValSource[A] -⚬ (ValSource[A] |*| ValSource[A]) =
        caseFst > swap

      choice(caseFst, caseSnd) > selectBy(ValSource.notifyAction)
    }

    def dropUntilFirstDemand[A]: ValSource[A] -⚬ ValSource[A] = rec { self =>
        val caseDownstreamRequested: (Val[A] |*| ValSource[A]) -⚬ ValSource[A] = {
          val caseDownstreamClosed: (Val[A] |*| ValSource[A]) -⚬ Done      = joinMap(neglect, ValSource.close)
          val caseDownstreamPulled: (Val[A] |*| ValSource[A]) -⚬ Polled[A] = injectR
          choice(caseDownstreamClosed, caseDownstreamPulled).pack
        }

        val caseNotRequestedYet: (Val[A] |*| ValSource[A]) -⚬ ValSource[A] = {
          id[Val[A] |*| ValSource[A]]
            .>.fst(neglect)
            .>(ValSource.delayBy)
            .>(self)
        }

        val goElem: (Val[A] |*| ValSource[A]) -⚬ ValSource[A] =
          choice(caseDownstreamRequested, caseNotRequestedYet)
            .>(selectSignaledOrNot(Source.negativeSource))

        id                               [    ValSource[A]                    ]
          .unpack                     .to[ Done |&| Polled[A]                 ]
          .chooseR                    .to[ Done |+| (Val[A] |*| ValSource[A]) ]
          .either(empty[A], goElem)   .to[    ValSource[A]                    ]
    }

    def broadcast[A]: ValSource[A] -⚬ PUnlimited[ValSource[A]] = rec { self =>
      val case0: ValSource[A] -⚬ Done                                                    = ValSource.close
      val case1: ValSource[A] -⚬ ValSource[A]                                            = id
      val caseN: ValSource[A] -⚬ (PUnlimited[ValSource[A]] |*| PUnlimited[ValSource[A]]) = dup > par(self, self)

      dropUntilFirstDemand > PUnlimited.create(case0, case1, caseN)
    }

    private[ValSource] type DemandingTree[K, V] = Tree[K, ValDrain.Pulling[V]]
    private[ValSource] object DemandingTree {
      type DT[K, V] = DemandingTree[K, V]
      type NeDT[K, V] = NonEmptyTree[K, ValDrain.Pulling[V]]

      def dispatch[K, V](using Ordering[K]): ((Val[K] |*| Val[V]) |*| DT[K, V]) -⚬ (Done |*| DT[K, V]) =
        Tree.update(ValDrain.Pulling.supply[V].>.left(need > done) > PMaybe.fromEither)
          .>.fst(PMaybe.neglect)

      def dispatchNE[K: Ordering, V]: ((Val[K] |*| Val[V]) |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        NonEmptyTree.update(
          ValDrain.Pulling.supply[V].>.left(need > done) > PMaybe.fromEither,
          ifAbsent = neglect,
        )

      def dispatchNE[A, K: Ordering, V](
        f: Val[A] -⚬ (Val[K] |*| Val[V]),
      ): (Val[A] |*| NeDT[K, V]) -⚬ PMaybe[NeDT[K, V]] =
        id                                     [       Val[A]        |*| NeDT[K, V]  ]
          .>.fst(f)                         .to[ (Val[K] |*| Val[V]) |*| NeDT[K, V]  ]
          .>(dispatchNE)                    .to[                  PMaybe[NeDT[K, V]] ]

      def addPulling[K, V](using Ordering[K]): ((Val[K] |*| ValDrain.Pulling[V]) |*| DT[K, V]) -⚬ DT[K, V] =
        Tree.insertOrUpdate(ValDrain.Pulling.contraDup)

      def clear[K, V]: DT[K, V] -⚬ Done =
        Tree.clear(ValDrain.Pulling.close > need > done)

      def clearNE[K, V]: NeDT[K, V] -⚬ Done =
        NonEmptyTree.clear(ValDrain.Pulling.close > need > done)

      def addSubscriber[K, V](using Ordering[K]): ((Val[K] |*| -[ValSource[V]]) |*| DT[K, V]) -⚬ DT[K, V] =
        λ { case ((k |*| out) |*| tree) =>
          val drain: $[ValDrain[V]] =
            ValDrain.fromInvertedSource(out)
          drain.toEither switch {
            case Left(closing)  => tree alsoElim rInvertSignal(neglect(k) |*| closing)
            case Right(pulling) => addPulling((k |*| pulling) |*| tree)
          }
        }
    }

    opaque type BroadcastByKey[K, V] = Drain[Val[K] |*| -[ValSource[V]]] |*| Done
    object BroadcastByKey {
      def close[K, V]: BroadcastByKey[K, V] -⚬ Done =
        elimFst(Drain.close > need)

      def subscribe[K, V](k: K): BroadcastByKey[K, V] -⚬ (BroadcastByKey[K, V] |*| ValSource[V]) = {
        val onDemand: Drain.Pulling[Val[K] |*| -[ValSource[V]]] -⚬ (Drain[Val[K] |*| -[ValSource[V]]] |*| ValSource[V]) =
          id                                       [           Drain.Pulling[Val[K] |*| -[ValSource[V]]]                     ]
            .>(Drain.Pulling.warrant)           .to[ -[Val[K]  |*|   -[ValSource[V]]]  |*| Drain[Val[K] |*| -[ValSource[V]]] ]
            .>.fst(distributeInversion)         .to[ -[Val[K]] |*| -[-[ValSource[V]]]  |*| Drain[Val[K] |*| -[ValSource[V]]] ]
            .>.fst(elimFst(constNeg(k) > need)) .to[               -[-[ValSource[V]]]  |*| Drain[Val[K] |*| -[ValSource[V]]] ]
            .>.fst(die)                         .to[                   ValSource[V]    |*| Drain[Val[K] |*| -[ValSource[V]]] ]
            .swap                               .to[ Drain[Val[K] |*| -[ValSource[V]]] |*|           ValSource[V]            ]

        val onUnsubscribed: Need -⚬ (Drain[Val[K] |*| -[ValSource[V]]] |*| ValSource[V]) =
          id[Need] > Drain.closed > introSnd(done > ValSource.empty[V])

        id[ Drain[Val[K] |*| -[ValSource[V]]] |*| Done ]
          .>.fst(Drain.switch(onUnsubscribed, onDemand))
          .>(IX)
      }
    }

    private def subscribeByKey[A, K, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    )(using
      Ordering[K],
    ): (ValSource[A] |*| Source[Val[K] |*| -[ValSource[V]]]) -⚬ Done = {
      import ValSource.{DemandingTree => DT}
      import DemandingTree.NeDT
      type KSubs = Val[K] |*| -[ValSource[V]]

      val discardSubscriber: KSubs -⚬ One =
        λ { case (k |*| out) => (k > dsl.neglect > ValSource.empty[V]) supplyTo out }

      def onUpstream(
        goRec: ((Polled[A] |*| Source.Polled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| Source.Polled[KSubs]) |*| DT[K, V]) -⚬ Done =
        λ { case ((polled |*| kSubs) |*| tree) =>
          polled switch {
            case Left(closed) =>
              joinAll(
                closed,
                Source.Polled.close(discardSubscriber > done)(kSubs),
                DT.clear(tree),
              )
            case Right(a |*| as) =>
              val (dispatched |*| tree1) = DT.dispatch(f(a) |*| tree)
              val polled = delayedPoll(dispatched |*| as)
              goRec((polled |*| kSubs) |*| tree1)
          }
        }

      val feedToNEDT: (Polled[A] |*| NeDT[K, V]) -⚬ Done =
        Source.Polled.feedTo(DT.dispatchNE(f)) > joinMap(id, Maybe.neglect(DT.clearNE))

      val forward: (Polled[A] |*| DT[K, V]) -⚬ Done =
        λ { case (polled |*| tree) =>
          tree switch {
            case Left(empty) => Polled.close(polled) alsoJoin empty
            case Right(tree) => feedToNEDT(polled |*| tree)
          }
        }

      def onSubs(
        goRec: ((Polled[A] |*| Source.Polled[KSubs]) |*| DT[K, V]) -⚬ Done,
      ): ((Polled[A] |*| Source.Polled[KSubs]) |*| DT[K, V]) -⚬ Done =
        λ { case (vals |*| subs) |*| tree =>
          subs switch {
            case Left(closed) =>
              forward(vals |*| tree) alsoJoin closed
            case Right(sub |*| subs) =>
              val tree1  = DT.addSubscriber(sub |*| tree)
              val subs1 = Source.poll(subs)
              goRec((vals |*| subs1) |*| tree1)
          }
        }

      val go: ((Polled[A] |*| Source.Polled[KSubs]) |*| DT[K, V]) -⚬ Done = rec { self =>
        import Source.Polled.positivePolled

        given SignalingJunction.Positive[KSubs] =
          SignalingJunction.Positive.byFst[Val[K], -[ValSource[V]]]

        λ { case (vals |*| subs) |*| tree =>
          ((vals |*| subs) > lib.race) switch {
            case Left (vals |*| subs) => onUpstream(self)((vals |*| subs) |*| tree)
            case Right(vals |*| subs) => onSubs(self)((vals |*| subs) |*| tree)
          }
        }
      }

      λ { case (vals |*| subscribers) =>
        go(
          ValSource.poll(vals) |*|
          Source.poll(subscribers) |*|
          one > done > Tree.empty[K, ValDrain.Pulling[V]]
        )
      }
    }

    def broadcastByKey[A, K: Ordering, V](
      f: Val[A] -⚬ (Val[K] |*| Val[V])
    ): ValSource[A] -⚬ BroadcastByKey[K, V] = {
      val lInvert: One -⚬ (Source[Val[K] |*| -[ValSource[V]]] |*| Drain[Val[K] |*| -[ValSource[V]]]) =
        lInvertSource

      λ { src =>
        val (subscriptions |*| subscribers) = one > lInvert
        subscribers |*| subscribeByKey(f)(src |*| subscriptions)
      }
    }

    object Polled {
      def close[A]: Polled[A] -⚬ Done =
        Source.Polled.close(dsl.neglect[A])

      def empty[A]: Done -⚬ Polled[A] =
        Source.Polled.empty

      def cons[A]: (Val[A] |*| ValSource[A]) -⚬ Polled[A] =
        Source.Polled.cons

      def unpoll[A]: Polled[A] -⚬ ValSource[A] =
        Source.Polled.unpoll[Val[A]]

      def delayBy[A]: (Done |*| Polled[A]) -⚬ Polled[A] =
        Source.Polled.delayBy

      implicit def positivePolled[A]: SignalingJunction.Positive[Polled[A]] =
        Source.Polled.positivePolled[Val[A]]

      /** Merges two [[Polled]]s into one.
        * Left-biased: whenever there is a value available from both upstreams, favors the first one.
        *
        * @param mergeSources left-biased merge of two [[ValSource]]s.
        */
      def merge[A](
        mergeSources: (ValSource[A] |*| ValSource[A]) -⚬ ValSource[A],
      ): (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        Source.Polled.merge(mergeSources)
    }
  }

  object ValDrain {
    type Pulling[A] = Drain.Pulling[Val[A]]

    def close[A]: ValDrain[A] -⚬ Need =
      Drain.close[Val[A]]

    def pulling[A]: Pulling[A] -⚬ ValDrain[A] =
      Drain.pulling[Val[A]]

    def toEither[A]: ValDrain[A] -⚬ (Need |+| Pulling[A]) =
      Drain.toEither[Val[A]]

    def fromEither[A]: (Need |+| Pulling[A]) -⚬ ValDrain[A] =
      Drain.fromEither[Val[A]]

    def fromInvertedSource[A]: -[ValSource[A]] -⚬ ValDrain[A] =
      λ { invSrc => invSrc unInvertWith (lInvertSource > swap) }

    /** Notifies when the drain has "made up its mind" whether to close or pull. */
    def notifyReady[A]: ValDrain[A] -⚬ (Ping |*| ValDrain[A]) =
      toEither > notifyEither > snd(fromEither)

    def onCloseAwait[A]: (Done |*| ValDrain[A]) -⚬ ValDrain[A] =
      Drain.onCloseAwait[Val[A]]

    private[ScalettoStreams] def contraDup0[A](
      contraDupPullings: (Pulling[A] |*| Pulling[A]) -⚬ Pulling[A]
    ): (ValDrain[A] |*| ValDrain[A]) -⚬ ValDrain[A] = {

      val goPulling: (ValDrain.Pulling[A] |*| ValDrain[A]) -⚬ ValDrain[A] =
        λ { case (pulling1 |*| drain2) =>
          ValDrain.pulling(
            drain2.toEither switch {
              case Left(closing2)  => pulling1 alsoElim (closing2 > need)
              case Right(pulling2) => contraDupPullings(pulling1 |*| pulling2)
            }
          )
        }

      val goFst: (ValDrain[A] |*| ValDrain[A]) -⚬ ValDrain[A] =
        λ { case (drain1 |*| drain2) =>
          drain1.toEither switch {
            case Left(closing)  => drain2 alsoElim (closing > need)
            case Right(pulling) => goPulling(pulling |*| drain2)
          }
        }

      λ { (drains: $[ValDrain[A] |*| ValDrain[A]]) =>
        drains > raceBy(ValDrain.notifyReady) switch {
          case Left (dr1 |*| dr2) => goFst(dr1 |*| dr2)
          case Right(dr1 |*| dr2) => goFst(dr2 |*| dr1)
        }
      }
    }

    /** Each value pulled by the resulting drain is duplicated and fed to both original drains. */
    def contraDup[A]: (ValDrain[A] |*| ValDrain[A]) -⚬ ValDrain[A] = rec { self =>
      contraDup0(ValDrain.Pulling.contraDup0(self))
    }

    object Pulling {
      def create[S, A](
        caseClose:    S -⚬ Need,
        caseWarrant:  S -⚬ (-[Val[A]] |*| ValDrain[A]),
      ): S -⚬ Pulling[A] =
        Drain.Pulling.create(caseClose, caseWarrant)

      def close[A]: Pulling[A] -⚬ Need =
        Drain.Pulling.close[Val[A]]

      def warrant[A]: Pulling[A] -⚬ (-[Val[A]] |*| ValDrain[A]) =
        Drain.Pulling.warrant[Val[A]]

      def supply[A]: (Val[A] |*| Pulling[A]) -⚬ (Need |+| Pulling[A]) =
        λ { case (a |*| pulling) =>
          val na |*| drain = pulling > warrant
          drain.toEither alsoElim (a supplyTo na)
        }

      private[ScalettoStreams] def contraDup0[A](
        contraDupDrains: (ValDrain[A] |*| ValDrain[A]) -⚬ ValDrain[A]
      ): (Pulling[A] |*| Pulling[A]) -⚬ Pulling[A] = {
        val caseClose: (Pulling[A] |*| Pulling[A]) -⚬ Need =
          forkMapNeed(close, close)

        val caseWarrant: (Pulling[A] |*| Pulling[A]) -⚬ (Neg[A] |*| ValDrain[A]) =
          λ { case (p1 |*| p2) =>
            val (neg1 |*| drain1) = warrant(p1)
            val (neg2 |*| drain2) = warrant(p2)
            mergeDemands(neg1 |*| neg2) |*| contraDupDrains(drain1 |*| drain2)
          }

        create(caseClose, caseWarrant)
      }

      def contraDup[A]: (Pulling[A] |*| Pulling[A]) -⚬ Pulling[A] = rec { self =>
        contraDup0(ValDrain.contraDup0(self))
      }
    }
  }

  extension [A](drain: $[ValDrain[A]]) {
    @targetName("ValDrainToEither")
    def toEither(using SourcePos, LambdaContext): $[Need |+| ValDrain.Pulling[A]] =
      drain > ValDrain.toEither

    @targetName("ValDrainOnCloseAwait")
    def onCloseAwait(using SourcePos, LambdaContext)(that: $[Done]): $[ValDrain[A]] =
      (that |*| drain) > ValDrain.onCloseAwait
  }

  def rInvertValDrain[A]: (ValDrain[A] |*| ValSource[A]) -⚬ One =
    rInvertDrain[Val[A]]

  def lInvertValSource[A]: One -⚬ (ValSource[A] |*| ValDrain[A]) =
    lInvertSource[Val[A]]

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
  def relayCompletion[A, B]: (ValSource[A] |*| ValDrain[B]) -⚬ (One |+| ((Val[A] |*| ValSource[A]) |*| (Neg[B] |*| ValDrain[B]))) =
    id                                [ ValSource[A] |*| (                   ValDrain[B]                                     )]
      .>.snd(unpack)               .to[ ValSource[A] |*| (Need   |+|                      (Need |&| (Neg[B] |*| ValDrain[B])))]
      .distributeL                 .to[(ValSource[A] |*|  Need)  |+|  (ValSource[A]   |*| (Need |&| (Neg[B] |*| ValDrain[B])))]
      .>.left.fst(ValSource.close) .to[(Done         |*|  Need)  |+|  (ValSource[A]   |*| (Need |&| (Neg[B] |*| ValDrain[B])))]
      .>.left(rInvertSignal)       .to[ One |+| (                      ValSource[A]   |*| (Need |&| (Neg[B] |*| ValDrain[B])))]
      .>.right.fst(ValSource.poll) .to[ One |+| ((Done |+| (Val[A] |*| ValSource[A])) |*| (Need |&| (Neg[B] |*| ValDrain[B])))]
      .>.right(matchingChoiceLR)   .to[ One |+| ((Done |*| Need) |+| ((Val[A] |*| ValSource[A]) |*| (Neg[B] |*| ValDrain[B])))]
      .>.right.left(rInvertSignal) .to[ One |+| (      One       |+| ((Val[A] |*| ValSource[A]) |*| (Neg[B] |*| ValDrain[B])))]
      .assocRL                     .to[(One |+|        One     ) |+| ((Val[A] |*| ValSource[A]) |*| (Neg[B] |*| ValDrain[B])) ]
      .>.left(either(id, id))      .to[     One                  |+| ((Val[A] |*| ValSource[A]) |*| (Neg[B] |*| ValDrain[B])) ]

  @deprecated("Renamed to ValSource")
  type Pollable[A] = ValSource[A]

  @deprecated("Renamed to ValSource")
  val Pollable: ValSource.type = ValSource
}
