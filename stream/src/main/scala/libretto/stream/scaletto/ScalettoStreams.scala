package libretto.stream.scaletto

import libretto.{CoreLib, InvertLib}
import libretto.lambda.util.{Exists, SourcePos}
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

      override val dsl         = scaletto
      override val coreLib     = lib
      override val scalettoLib = sLib
      override val underlying  = iStreams
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
  val underlying: InvertStreams & libretto.stream.InvertStreams[dsl.type, coreLib.type]

  private lazy val invertLib = InvertLib(coreLib)
  import invertLib.inversionDuality

  private lazy val Tree = BinarySearchTree(dsl, coreLib, scalettoLib)

  import dsl._
  import dsl.$._
  import coreLib._
  import scalettoLib.{_, given}
  import underlying._
  import Tree._

  export underlying.{lib => _, dsl => _, _}

  type ValSourceT[T, A] = SourceT[T, Val[A]]

  type ValSource[A] = Source[Val[A]]
  type ValDrain[A]  = Drain[Val[A]]
  type ValStream[A] = Stream[Val[A]]
  type ValSink[A]   = Sink[Val[A]]

  object ValSourceT {
    type Polled[T, A] = SourceT.Polled[T, Val[A]]

    def from[S, T, A](
      onClose: S -⚬ T,
      onPoll: S -⚬ (T |+| (Val[A] |*| ValSourceT[T, A]))
    ): S -⚬ ValSourceT[T, A] =
      SourceT.from(onClose, onPoll)

    def fromChoice[T, A]: (T |&| (T |+| (Val[A] |*| ValSourceT[T, A]))) -⚬ ValSourceT[T, A] =
      SourceT.fromChoice[T, Val[A]]

    def empty[T, A]: T -⚬ ValSourceT[T, A] =
      SourceT.empty[T, Val[A]]

    def close[T, A]: ValSourceT[T, A] -⚬ T =
      SourceT.close[T, Val[A]]

    def poll[T, A]: ValSourceT[T, A] -⚬ Polled[T, A] =
      SourceT.poll[T, Val[A]]

    def fromList[T, A]: (Val[List[A]] |*| Detained[T]) -⚬ ValSourceT[T, A] = rec { fromList =>
      val uncons: List[A] => Option[(A, List[A])] = _ match {
        case a :: as => Some((a, as))
        case Nil => None
      }

      val close: (Val[List[A]] |*| Detained[T]) -⚬ T =
        λ { case as |*| t =>
          t.releaseWhen(neglect(as))
        }

      val poll: (Val[List[A]] |*| Detained[T]) -⚬ Polled[T, A] =
        λ { case as |*| t =>
          as > mapVal(uncons) > optionToPMaybe > PMaybe.toEither switch {
            case Left(nil)      => t.releaseWhen(nil) > Polled.empty[T, A]
            case Right(a ** as) => Polled.cons(a |*| fromList(as |*| t))
          }
        }

      ValSourceT.from(close, poll)
    }

    def take[T, A](n: Int): ValSourceT[T, A] -⚬ (Val[Int] |*| ValSourceT[T, A]) =
      introFst(const(n)) > take

    /** Cut off the upstream after a given number _n_ of elements.
     *  The number on the outport is _n - m_, where _m_ is the number of elements actually served.
     */
    def take[T, A]: (Val[Int] |*| ValSourceT[T, A]) -⚬ (Val[Int] |*| ValSourceT[T, A]) = rec { take =>
      λ { case n |*| src =>
        decrement(n) switch {
          case Left(done) =>
            constVal(0)(done) |*| empty(close(src))
          case Right(n0)  =>
            producing { case remaining |*| as =>
              (fromChoice >>: as) switch {
                case Left(closing) =>
                  returning(
                    remaining := n0,
                    closing   := close(src),
                  )
                case Right(pulling) =>
                  (remaining |*| pulling) :=
                    poll(src) switch {
                      case Left(t) =>
                        n0 |*| Polled.empty(t)
                      case Right(a |*| as) =>
                        val (n1 |*| as1) = take(n0 |*| as)
                        n1 |*| Polled.cons(a |*| as1)
                    }
              }
            }
        }
      }
    }

    def forEachSequentially[T, A](f: Val[A] -⚬ Done): ValSourceT[T, A] -⚬ (Done |*| T) =
      SourceT.forEachSequentially(f)

    object Polled {
      def empty[T, A]: T -⚬ Polled[T, A] =
        SourceT.Polled.empty[T, Val[A]]

      def cons[T, A]: (Val[A] |*| ValSourceT[T, A]) -⚬ Polled[T, A] =
        SourceT.Polled.cons[T, Val[A]]
    }
  }

  object ValSource {
    type Polled[A] = Source.Polled[Val[A]]

    def from[Z, A](
      onClose: Z -⚬ Done,
      onPoll: Z -⚬ (Done |+| (Val[A] |*| ValSource[A]))
    ): Z -⚬ ValSource[A] =
      Source.from(onClose, onPoll)

    def fromChoice[A]: (Done |&| Polled[A]) -⚬ ValSource[A] =
      Source.fromChoice[Val[A]]

    def toChoice[A]: ValSource[A] -⚬ (Done |&| Polled[A]) =
      Source.toChoice[Val[A]]

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

    def singleton[A]: (Val[A] |*| Done) -⚬ ValSource[A] =
      Source.singleton[Val[A]]

    def fromLList[A]: LList[Val[A]] -⚬ ValSource[A] =
      Source.fromLList[Val[A]]

    def detain[A]: ValSource[A] -⚬ Detained[ValSource[A]] =
      Source.detain[Val[A]]

    /** Delays the first action ([[poll]] or [[close]]) until the [[Done]] signal is received. */
    def delayBy[A]: (Done |*| ValSource[A]) -⚬ ValSource[A] =
      Source.delayBy[Val[A]]

    def delayable[A]: ValSource[A] -⚬ (Need |*| ValSource[A]) =
      Source.delayable[Val[A]]

    /** Delays the final [[Done]] signal sent when upstream is shutdown
     *  until the given [[Done]] signal is received.
     */
    def delayClosedBy[A]: (Done |*| ValSource[A]) -⚬ ValSource[A] =
      Source.delayClosedBy[Val[A]]

    def notifyAction[A]: (Pong |*| ValSource[A]) -⚬ ValSource[A] =
      Source.notifyAction[Val[A]]

    /** Notifies when the upstream is fully closed. */
    def notifyUpstreamClosed[A]: ValSource[A] -⚬ (Ping |*| ValSource[A]) =
      Source.notifyUpstreamClosed[Val[A]]

    def delay[A](d: FiniteDuration): ValSource[A] -⚬ ValSource[A] = {
      id                                           [          ValSource[A] ]
        .<(notifyAction)                      .from[ Pong |*| ValSource[A] ]
        .<.fst(strengthenPong)                .from[ Need |*| ValSource[A] ]
        .<.fst(delayNeed(d))                  .from[ Need |*| ValSource[A] ]
        .<(delayable)                         .from[          ValSource[A] ]
    }

    def fromList[A]: Val[List[A]] -⚬ ValSource[A] = rec { fromList =>
      val uncons: List[A] => Option[(A, List[A])] = _ match {
        case a :: as => Some((a, as))
        case Nil => None
      }

      val close: Val[List[A]] -⚬ Done = neglect

      val poll: Val[List[A]] -⚬ Polled[A] =
        λ { as =>
          as > mapVal(uncons) > optionToPMaybe > PMaybe.toEither switch {
            case Left(nil)     => nil > Polled.empty[A]
            case Right(h ** t) => Polled.cons(h |*| fromList(t))
          }
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
        λ { case as |*| acc =>
          poll(as) switch {
            case Left(closed) =>
              val res = acc > mapVal(_.reverse)
              res waitFor closed
            case Right(h |*| t) =>
              val acc1 = (h ** acc) > mapVal(_ :: _)
              self(t |*| acc1)
          }
        }
      }

      λ { as =>
        val nil = one > const(List.empty[A])
        go(as |*| nil)
      }
    }

    def repeatedly[A, B](f: A -⚬ Val[B])(using CloseableCosemigroup[A]): A -⚬ ValSource[B] =
      Source.repeatedly[A, Val[B]](f)

    def map[A, B](f: A => B): ValSource[A] -⚬ ValSource[B] = {
      val g: Val[A] -⚬ Val[B] = mapVal(f)
      Source.map(g)
    }

    def take[A](n: Int): ValSource[A] -⚬ ValSource[A] =
      ValSourceT.take[Done, A](n) > fst(neglect) > delayClosedBy

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
        unliftPair[S, A] > mapVal(f) > liftPair[S, B]

      val inner: (Val[S] |*| ValSource[A]) -⚬ ValSource[B] = rec { self =>
        val close: (Val[S] |*| ValSource[A]) -⚬ Done =
          joinMap(neglect, ValSource.close)

        val poll:(Val[S] |*| ValSource[A]) -⚬ (Done |+| (Val[B] |*| ValSource[B])) =
          λ { case (s |*| as) =>
            ValSource.poll(as) switch {
              case Left(closed) =>
                injectL(neglect(s) alsoJoin closed)
              case Right(a |*| as) =>
                val (s1 |*| b) = ff(s |*| a)
                injectR(b |*| self(s1 |*| as))
            }
          }

        ValSource.from(close, poll)
      }

      λ { as =>
        val s = one > const(initialState)
        inner(s |*| as)
      }
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
      // the case when the first output polls or closes before the second output does
      val goFst: ValSource[A] -⚬ (ValSource[A] |*| ValSource[A]) =
        λ { src =>
          producing { case (out1 |*| out2) =>
            (ValSource.fromChoice >>: out1) switch {
              case Left(closing)  =>
                (src :>: out2) alsoElim (done >>: closing)
              case Right(polling1) =>
                val polled = ValSource.poll(src)
                (ValSource.fromChoice >>: out2) switch {
                  case Left(closing2) =>
                    (polled :>: polling1) alsoElim (done >>: closing2)
                  case Right(polling2) =>
                    Polled.dup(self)(polled) :>: (polling1 |*| polling2)
                }
            }
          }
        }

      λ { src =>
        producing { case out1 |*| out2 =>
          (selectBy(ValSource.notifyAction[A]) >>: (out1 |*| out2)) switch {
            case Left (out1 |*| out2) => goFst(src) :>: (out1 |*| out2)
            case Right(out1 |*| out2) => goFst(src) :>: (out2 |*| out1)
          }
        }
      }
    }

    def tap[A]: ValSource[A] -⚬ (ValSource[A] |*| LList[Val[A]]) =
      Source.tap[Val[A]]

    def terminateWith[A, T]: (ValSource[A] |*| Detained[T]) -⚬ ValSourceT[T, A] =
      Source.terminateWith[Val[A], T]

    def prefetch[A](n: Int): ValSource[A] -⚬ ValSource[A] =
      Source.prefetch[Val[A]](n)(neglect, Exists(inversionDuality[LList[Done]]))

    def dropUntilFirstDemand[A]: ValSource[A] -⚬ ValSource[A] = rec { self =>
        val caseDownstreamRequested: (Val[A] |*| ValSource[A]) -⚬ ValSource[A] = {
          val caseDownstreamClosed: (Val[A] |*| ValSource[A]) -⚬ Done      = joinMap(neglect, ValSource.close)
          val caseDownstreamPulled: (Val[A] |*| ValSource[A]) -⚬ Polled[A] = injectR
          ValSource.from(caseDownstreamClosed, caseDownstreamPulled)
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

        poll > either(empty[A], goElem)
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

      def dup[A](
        dupSource: ValSource[A] -⚬ (ValSource[A] |*| ValSource[A]),
      ): Polled[A] -⚬ (Polled[A] |*| Polled[A]) =
        λ { polled =>
          polled switch {
            case Left(+(closed)) =>
              Polled.empty(closed) |*| Polled.empty(closed)
            case Right(+(a) |*| as) =>
              val (t1 |*| t2) = dupSource(as)
              Polled.cons(a |*| t1) |*| Polled.cons(a |*| t2)
          }
        }
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

  def rInvertValStream[A]: (ValStream[A] |*| ValSink[A]) -⚬ One =
    rInvertStream[Val[A]]

  def lInvertValSink[A]: One -⚬ (ValSink[A] |*| ValStream[A]) =
    lInvertSink[Val[A]]

  /** If either the source or the drain is completed, complete the other one and be done.
    * Otherwise, expose their offer and demand, respectively.
    */
  def relayCompletion[A, B]: (ValSource[A] |*| ValDrain[B]) -⚬ (One |+| ((Val[A] |*| ValSource[A]) |*| (Neg[B] |*| ValDrain[B]))) =
    λ { case (src |*| drn) =>
      drn.toEither switch {
        case Left(closing) =>
          injectL(rInvertSignal(ValSource.close(src) |*| closing))
        case Right(pulling) =>
          ValSource.poll(src) switch {
            case Left(closed) =>
              injectL(rInvertSignal(closed |*| ValDrain.Pulling.close(pulling)))
            case Right(a |*| as) =>
              val b |*| bs = ValDrain.Pulling.warrant(pulling)
              injectR((a |*| as) |*| (b |*| bs))
          }
      }
    }

  @deprecated("Renamed to ValSource")
  type Pollable[A] = ValSource[A]

  @deprecated("Renamed to ValSource")
  val Pollable: ValSource.type = ValSource
}
