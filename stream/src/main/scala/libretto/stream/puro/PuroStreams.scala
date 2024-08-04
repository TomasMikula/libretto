package libretto.stream.puro

import libretto.puro.{Puro, PuroLib}
import libretto.lambda.util.Exists

object PuroStreams {
  def apply(
    dsl: Puro,
    lib: PuroLib[dsl.type],
  )
  : PuroStreams[dsl.type, lib.type] =
    new PuroStreams(dsl, lib)
}

class PuroStreams[DSL <: Puro, Lib <: PuroLib[DSL]](
  val dsl: DSL,
  val lib: Lib & PuroLib[dsl.type],
) {
  import dsl.*
  import lib.{*, given}

  private type StreamLeaderF[S, T, A, X]   = S |+| (T |&| (A |*| X))
  private type StreamFollowerF[S, T, A, X] = S |&| (T |+| (A |*| X))

  opaque type StreamLeader[S, T, A]   = Rec[StreamLeaderF[S, T, A, _]]
  opaque type StreamFollower[S, T, A] = Rec[StreamFollowerF[S, T, A, _]]

  opaque type StreamT[T, A] = StreamLeader[T, T, A]
  opaque type SourceT[T, A] = StreamFollower[T, T, A]

  opaque type Stream[A] = StreamT[Done, A]
  opaque type Source[A] = SourceT[Done, A]

  opaque type Drain[A] = StreamT[Need, -[A]]
  opaque type Sink[A]  = SourceT[Need, -[A]]

  object StreamLeader {
    def pack[S, T, A]: StreamLeaderF[S, T, A, StreamLeader[S, T, A]] -⚬ StreamLeader[S, T, A] =
      dsl.pack

    def unpack[S, T, A]: StreamLeader[S, T, A] -⚬ StreamLeaderF[S, T, A, StreamLeader[S, T, A]] =
      dsl.unpack

    def closed[S, T, A]: S -⚬ StreamLeader[S, T, A] =
      injectL > pack

    def next[S, T, A]: (T |&| (A |*| StreamLeader[S, T, A])) -⚬ StreamLeader[S, T, A] =
      injectR > pack

    def switch[S, T, A, R](
      onClose: S -⚬ R,
      onNext: (T |&| (A |*| StreamLeader[S, T, A])) -⚬ R,
    ): StreamLeader[S, T, A] -⚬ R =
      unpack > either(onClose, onNext)
  }

  object StreamFollower {
    def pack[S, T, A]: StreamFollowerF[S, T, A, StreamFollower[S, T, A]] -⚬ StreamFollower[S, T, A] =
      dsl.pack

    def unpack[S, T, A]: StreamFollower[S, T, A] -⚬ StreamFollowerF[S, T, A, StreamFollower[S, T, A]] =
      dsl.unpack
  }

  object StreamT {
    def fromEither[T, A]: (T |+| (T |&| (A |*| StreamT[T, A]))) -⚬ StreamT[T, A] =
      StreamLeader.pack[T, T, A]

    def toEither[T, A]: StreamT[T, A] -⚬ (T |+| (T |&| (A |*| StreamT[T, A]))) =
      StreamLeader.unpack

    def closed[T, A]: T -⚬ StreamT[T, A] =
      StreamLeader.closed[T, T, A]

    def next[T, A]: (T |&| (A |*| StreamT[T, A])) -⚬ StreamT[T, A] =
      StreamLeader.next[T, T, A]

    def switch[T, A, R](
      onClose: T -⚬ R,
      onNext: (T |&| (A |*| StreamT[T, A])) -⚬ R,
    ): StreamT[T, A] -⚬ R =
      StreamLeader.switch(onClose, onNext)
  }

  object Stream {
    type Offer[A] = Done |&| (A |*| Stream[A])

    def fromLeader[A]: StreamLeader[Done, Done, A] -⚬ Stream[A] = id
    def toLeader[A]  : Stream[A] -⚬ StreamLeader[Done, Done, A] = id

    def toEither[A]: Stream[A] -⚬ (Done |+| Offer[A]) =
      StreamLeader.unpack

    def collectAll[A]: Stream[A] -⚬ (LList[A] |*| Done) = rec { collectAll =>
      toEither > either(
        introFst(LList.nil[A]),
        chooseR > snd(collectAll) > assocRL > fst(LList.cons)
      )
    }
  }

  object SourceT {
    type Polled[T, A] = T |+| (A |*| SourceT[T, A])

    def fromChoice[T, A]: (T |&| (T |+| (A |*| SourceT[T, A]))) -⚬ SourceT[T, A] =
      StreamFollower.pack

    def toChoice[T, A]: SourceT[T, A] -⚬ (T |&| (T |+| (A |*| SourceT[T, A]))) =
      StreamFollower.unpack

    def from[S, T, A](
      onClose: S -⚬ T,
      onPoll: S -⚬ Polled[T, A],
    ): S -⚬ SourceT[T, A] =
      choice(onClose, onPoll) > fromChoice

    def empty[T, A]: T -⚬ SourceT[T, A] =
      from[T, T, A](id[T], injectL)

    def close[T, A]: SourceT[T, A] -⚬ T =
      StreamFollower.unpack > chooseL

    def poll[T, A]: SourceT[T, A] -⚬ Polled[T, A] =
      StreamFollower.unpack > chooseR

    def map[T, A, B](f: A -⚬ B): SourceT[T, A] -⚬ SourceT[T, B] = rec { self =>
      from(
        onClose = close[T, A],
        onPoll  = poll[T, A] > either(
          Polled.empty[T, B],
          par(f, self) > Polled.cons[T, B],
        ),
      )
    }

    def toLList[T, A]: SourceT[T, A] -⚬ (LList[A] |*| T) = rec { self =>
      λ { src =>
        poll(src) either {
          case Left(t) =>
            constant(LList.nil) |*| t
          case Right(a |*| tl) =>
            val (as |*| t) = self(tl)
            LList.cons(a |*| as) |*| t
        }
      }
    }

    /** Concatenates the two sources.
     *
     * @param carryOver defines how the terminator of the first source is carried over to the second one.
     */
    def concatenate[T, A](
      carryOver: (T |*| SourceT[T, A]) -⚬ SourceT[T, A],
    ): (SourceT[T, A] |*| SourceT[T, A]) -⚬ SourceT[T, A] =
      rec { self =>
        val onClose: (SourceT[T, A] |*| SourceT[T, A]) -⚬ T =
          fst(SourceT.close) > carryOver > SourceT.close

        val onPoll: (SourceT[T, A] |*| SourceT[T, A]) -⚬ Polled[T, A] =
          λ { case src1 |*| src2 =>
            poll(src1) either {
              case Left(t) =>
                poll(carryOver(t |*| src2))
              case Right(a |*| as) =>
                Polled.cons(a |*| self(as |*| src2))
            }
          }

        from(onClose, onPoll)
      }

    def delayUntilPing[T, A]: (Ping |*| SourceT[T, A]) -⚬ SourceT[T, A] =
      snd(toChoice) > delayChoiceUntilPing > fromChoice

    /** Delays each next poll or close until the previously emitted element signalled. */
    def sequence[T, A](using A: Signaling.Positive[A]): SourceT[T, A] -⚬ SourceT[T, A] =
      map(A.notifyPosFst) > sequenceByPing[T, A]

    /** Delays each next poll or close until the [[Ping]] from the previously emitted element. */
    def sequenceByPing[T, A]: SourceT[T, Ping |*| A] -⚬ SourceT[T, A] = {
      def go: (Ping |*| SourceT[T, Ping |*| A]) -⚬ SourceT[T, A] = rec { go =>
        val onPoll: SourceT[T, Ping |*| A] -⚬ Polled[T, A] =
          λ { as =>
            poll(as) either {
              case Left(t) =>
                Polled.empty(t)
              case Right((p |*| a) |*| as) =>
                Polled.cons(a |*| go(p |*| as))
            }
          }

        delayUntilPing[T, Ping |*| A] > from(close[T, Ping |*| A], onPoll)
      }

      introFst(ping) > go
    }

    def fold[T, A](using A: Monoid[A]): SourceT[T, A] -⚬ (A |*| T) = {
      def go: (A |*| SourceT[T, A]) -⚬ (A |*| T) = rec { go =>
        λ { case a0 |*| as =>
          poll(as) either {
            case Left(t)          => a0 |*| t
            case Right(a1 |*| as) => go((A.combine(a0 |*| a1)) |*| as)
          }
        }
      }

      introFst(A.unit) > go
    }

    def mapSequence[T, A, B](f: A -⚬ (Ping |*| B)): SourceT[T, A] -⚬ SourceT[T, B] =
      map(f) > sequenceByPing

    def mapSequentially[T, A, B: Signaling.Positive](f: A -⚬ B): SourceT[T, A] -⚬ SourceT[T, B] =
      map(f) > sequence

    def forEachSequentially[T, A](f: A -⚬ Done): SourceT[T, A] -⚬ (Done |*| T) =
      map(f) > sequence > fold

    def pullN[T, A](n: Int): SourceT[T, A] -⚬ ((LList[A] |*| T) |+| (LList1[A] |*| SourceT[T, A])) = {
      require(n > 0, s"n must be positive")

      λ { src =>
        poll(src) either {
          case Left(t) =>
            injectL(constant(LList.nil[A]) |*| t)
          case Right(a |*| as) =>
            if (n == 1)
              injectR(LList1.singleton(a) |*| as)
            else
              pullN(n-1)(as) either {
                case Left(as |*| t)     => injectL(LList.cons(a |*| as) |*| t)
                case Right(as |*| tail) => injectR(LList1.cons1(a |*| as) |*| tail)
              }
        }
      }
    }

    def groups[T, A](groupSize: Int): SourceT[T, A] -⚬ SourceT[T, LList1[A]] = rec { self =>
      require(groupSize > 0, s"group size must be positive")

      val onPull: SourceT[T, A] -⚬ Polled[T, LList1[A]] =
        pullN(groupSize) > either(
          λ { case elems |*| closed =>
            (closed |*| elems) |> LList.switchWithL(
              Polled.empty,
              λ { case closed |*| (h |*| t) => Polled.cons(LList1.cons(h |*| t) |*| SourceT.empty[T, LList1[A]](closed)) },
            )
          },
          snd(self) > Polled.cons[T, LList1[A]],
        )

      SourceT.from(close, onPull)
    }

    def take[T, A](n: Int): SourceT[T, A] -⚬ (UInt31 |*| SourceT[T, A]) =
      introFst(done > UInt31(n)) > take

    /** Cut off the upstream after a given number _n_ of elements.
     *  The number on the outport is _n - m_, where _m_ is the number of elements actually served.
     */
    def take[T, A]: (UInt31 |*| SourceT[T, A]) -⚬ (UInt31 |*| SourceT[T, A]) = rec { take =>
      def go1: (UInt31 |*| SourceT[T, A]) -⚬ (UInt31 |*| SourceT[T, A]) = {
        val onClose: (UInt31 |*| SourceT[T, A]) -⚬ (UInt31 |*| T) =
          par(UInt31.increment, close)
        val onPoll: (UInt31 |*| SourceT[T, A]) -⚬ (UInt31 |*| Polled[T, A]) =
          λ { case n0 |*| src =>
            poll(src) either {
              case Left(t) =>
                UInt31.increment(n0) |*| Polled.empty(t)
              case Right(a |*| as) =>
                val (n1 |*| as1) = take(n0 |*| as)
                n1 |*| Polled.cons(a |*| as1)
            }
          }
        choice(onClose, onPoll) > coDistributeL > snd(SourceT.fromChoice)
      }

      λ { case n |*| src =>
        UInt31.decrement(n) either {
          case Left(done) =>
            UInt31(0)(done) |*| empty[T, A](close(src))
          case Right(n0) =>
            go1(n0 |*| src)
        }
      }
    }

    object Polled {
      def empty[T, A]: T -⚬ Polled[T, A] =
        injectL

      def cons[T, A]: (A |*| SourceT[T, A]) -⚬ Polled[T, A] =
        injectR
    }
  }

  object Source {
    type Polled[A] = Done |+| (A |*| Source[A])

    def fromFollower[A]: StreamFollower[Done, Done, A] -⚬ Source[A] = id
    def toFollower[A]  : Source[A] -⚬ StreamFollower[Done, Done, A] = id

    def fromSourceT[A]: SourceT[Done, A] -⚬ Source[A] = id
    def toSourceT[A]  : Source[A] -⚬ SourceT[Done, A] = id

    def fromChoice[A]: (Done |&| Polled[A]) -⚬ Source[A] =
      dsl.pack[StreamFollowerF[Done, Done, A, _]]

    def toChoice[A]: Source[A] -⚬ (Done |&| Polled[A]) =
      dsl.unpack[StreamFollowerF[Done, Done, A, _]]

    def from[A, B](
      onClose: A -⚬ Done,
      onPoll: A -⚬ Polled[B],
    ): A -⚬ Source[B] =
      choice(onClose, onPoll) > fromChoice

    def close[A]: Source[A] -⚬ Done =
      unpack > chooseL

    def poll[A]: Source[A] -⚬ Polled[A] =
      unpack > chooseR

    def delayedPoll[A: Junction.Positive]: (Done |*| Source[A]) -⚬ Polled[A] =
      id                                      [ Done |*|     Source[A]        ]
        .>(snd(unpack))                    .to[ Done |*| (Done |&| Polled[A]) ]
        .>(chooseRWhenDone)                .to[ Done |*|           Polled[A]  ]
        .>(Polled.delayBy[A])              .to[                    Polled[A]  ]

    def toLList[A]: Source[A] -⚬ (LList[A] |*| Done) =
      SourceT.toLList

    /** Polls and discards all elements. */
    def drain[A](using A: Closeable[A]): Source[A] -⚬ Done =
      rec { self =>
        poll[A] > either(id, joinMap(A.close, self))
      }

    private def emptyF[A]: Done -⚬ StreamFollowerF[Done, Done, A, Source[A]] =
      choice[Done, Done, Polled[A]](id, injectL)

    def empty[A]: Done -⚬ Source[A] =
      emptyF[A] > StreamFollower.pack

    def cons[A](neglect: A -⚬ Done): (A |*| Source[A]) -⚬ Source[A] = {
      val onClose: (A |*| Source[A]) -⚬ Done      = joinMap(neglect, Source.close)
      val onPoll:  (A |*| Source[A]) -⚬ Polled[A] = Polled.cons
      from(onClose, onPoll)
    }

    def cons[A](using A: Closeable[A]): (A |*| Source[A]) -⚬ Source[A] =
      cons[A](A.close)

    def singleton[A](using A: Closeable[A]): (A |*| Done) -⚬ Source[A] =
      from(
        onClose = fst(A.close) > join,
        onPoll  = Polled.singleton[A],
      )

    def fromLList[A](neglect: A -⚬ Done): LList[A] -⚬ Source[A] =
      rec { self => λ { as =>
        switch( as )
          .is { case LList.Nil(u) => Source.empty[A](done(u)) }
          .is { case LList.Cons(a |*| as) => Source.cons(neglect)(a |*| self(as)) }
          .end
      }}

    def fromLList[A](using A: Closeable[A]): LList[A] -⚬ Source[A] =
      fromLList(A.close)

    def of[A](as: (One -⚬ A)*)(using Closeable[A]): One -⚬ Source[A] =
      LList.of(as*) > fromLList

    def repeatedly[A, B](f: A -⚬ B)(using A: CloseableCosemigroup[A]): A -⚬ Source[B] =
      rec { self =>
        from(
          onClose = A.close,
          onPoll  = A.split > par(f, self) > Polled.cons,
        )
      }

    /** Signals the first action (i.e. [[poll]] or [[close]]) via a negative ([[Pong]]) signal. */
    def notifyAction[A]: (Pong |*| Source[A]) -⚬ Source[A] =
      snd(toChoice) > notifyChoice > fromChoice

    /** Notifies as soon as donwstream closes
     *  (without waiting for upstream to be fully shutdown)
     *  or when the upstream runs out of elements
     *  (again without waiting for upstream to be fully shutdown).
     */
    def notifyDownstreamClosed[A]: (Pong |*| Source[A]) -⚬ Source[A] = rec { self =>
      val onClose: (Pong |*| Source[A]) -⚬ Done =
        λ { case pong |*| src =>
          close(src) alsoElim dsl.pong(pong)
        }

      val onPoll: (Pong |*| Source[A]) -⚬ Polled[A] =
        λ { case pong |*| src =>
          poll(src) either {
            case Left(closed) =>
              Polled.empty(closed) alsoElim dsl.pong(pong)
            case Right(a |*| as) =>
              val tail = self(pong |*| as)
              Polled.cons(a |*| tail)
          }
        }

      choice(onClose, onPoll) > fromChoice
    }

    /** Notifies when upstream is fully shutdown
     *  (whether in response to downstream closing or upstream finished).
     */
    def notifyUpstreamClosed[A]: Source[A] -⚬ (Ping |*| Source[A]) = rec { self =>
      val onClose: Source[A] -⚬ (Ping |*| Done) =
        close > notifyDoneL

      val onPoll: Source[A] -⚬ (Ping |*| Polled[A]) =
        λ { src =>
          poll(src) either {
            case Left(closed) =>
              closed |> notifyDoneL > snd(Polled.empty)
            case Right(a |*| as) =>
              val (ping |*| as1) = self(as)
              ping |*| Polled.cons(a |*| as1)
          }
        }

      choice(onClose, onPoll) > coDistributeL > snd(fromChoice)
    }

    /** Delays the first action ([[poll]] or [[close]]) until the [[Done]] signal completes. */
    def delayBy[A](using ev: Junction.Positive[A]): (Done |*| Source[A]) -⚬ Source[A] =
      id                                           [  Done |*|      Source[A]                  ]
        .>(snd(toChoice))                       .to[  Done |*| (Done  |&|           Polled[A]) ]
        .>(delayChoiceUntilDone)                .to[ (Done |*|  Done) |&| (Done |*| Polled[A]) ]
        .>(|&|.bimap(join, Polled.delayBy[A]))  .to[       Done       |&|           Polled[A]  ]
        .>(fromChoice)                          .to[               Source[A]                   ]

    def delayable[A](using Junction.Positive[A]): Source[A] -⚬ (Need |*| Source[A]) =
      λ { src =>
        val (n |*| d) = $.one |> lInvertSignal
        n |*| ((d |*| src) |> delayBy)
      }

    /** Delays the final [[Done]] signal (signaling end of stream or completed [[close]]) until the given [[Done]]
      * signal completes.
      */
    def delayClosedBy[A]: (Done |*| Source[A]) -⚬ Source[A] = rec { self =>
      id                                                     [  Done |*|      Source[A]                  ]
        .>(snd(unpack))                                   .to[  Done |*| (Done  |&|           Polled[A]) ]
        .>(coFactorL)                                     .to[ (Done |*|  Done) |&| (Done |*| Polled[A]) ]
        .>(|&|.bimap(join, Polled.delayClosedBy_(self)))  .to[       Done       |&|           Polled[A]  ]
        .>(fromChoice)                                    .to[               Source[A]                   ]
    }

    /** Blocks the first action ([[poll]] or [[close]]) on this [[Source]] until released. */
    def detain[A: Junction.Positive]: Source[A] -⚬ Detained[Source[A]] =
      Detained(delayBy)

    /** Delays the final [[Done]] signal resulting from [[close]] or end of stream. */
    def detainClosed[A]: Source[A] -⚬ Detained[Source[A]] =
      Detained(delayClosedBy)

    def map[A, B](f: A -⚬ B): Source[A] -⚬ Source[B] = rec { self =>
      from(close[A], poll[A]./>.right(par(f, self)))
    }

    def mapWith[X, A, B](f: (X |*| A) -⚬ B)(using
      X: CloseableCosemigroup[X],
    ): (X |*| Source[A]) -⚬ Source[B] =
      rec { self =>
        val onClose: (X |*| Source[A]) -⚬ Done =
          joinMap(X.close, Source.close)

        val onPoll: (X |*| Source[A]) -⚬ Polled[B] =
          λ { case +(x) |*| as =>
            poll(as) either {
              case Left(closed) =>
                Polled.empty(joinAll(X.close(x), closed))
              case Right(a |*| as) =>
                Polled.cons(f(x |*| a) |*| self(x |*| as))
            }
          }

        from(onClose, onPoll)
      }

    def mapSequence[A, B](f: A -⚬ (Ping |*| B)): Source[A] -⚬ Source[B] =
      SourceT.mapSequence(f)

    def mapSequentially[A, B: Signaling.Positive](f: A -⚬ B): Source[A] -⚬ Source[B] =
      mapSequence(f > notifyPosFst)

    def forEachSequentially[A](f: A -⚬ Done): Source[A] -⚬ Done =
      SourceT.forEachSequentially(f) > join

    def pullN[A](n: Int): Source[A] -⚬ ((LList[A] |*| Done) |+| (LList1[A] |*| Source[A])) =
      SourceT.pullN(n)

    def groups[A](groupSize: Int): Source[A] -⚬ Source[LList1[A]] =
      SourceT.groups(groupSize)

    def take[A](n: Int): Source[A] -⚬ Source[A] =
      SourceT.take[Done, A](n) > fst(UInt31.neglect) > delayClosedBy

    /** Concatenates the two sources.
     *
     * @param carryOver defines how the terminator of the first source is carried over to the second one.
     */
    def concatenate[A](carryOver: (Done |*| Source[A]) -⚬ Source[A]): (Source[A] |*| Source[A]) -⚬ Source[A] =
      SourceT.concatenate[Done, A](carryOver)

    /** Concatenates the two sources.
     *  Before pulling from or closing the second one, waits until the first one is fully closed.
     */
    def concatStrict[A: Junction.Positive]: (Source[A] |*| Source[A]) -⚬ Source[A] =
      concatenate(delayBy)

    /** Concatenates the two sources.
     *  Does not wait for the first source to be fully closed before pulling or closing the second one.
     */
    def concatLax[A]: (Source[A] |*| Source[A]) -⚬ Source[A] =
      concatenate(delayClosedBy)

    /** Alias for [[concatLax]].
     *  Does not wait for the first source to be fully closed before pulling or closing the second one.
     */
    def concat[A]: (Source[A] |*| Source[A]) -⚬ Source[A] =
      concatLax[A]

    def flatten[A](carryOver: (Done |*| Source[A]) -⚬ Source[A]): Source[Source[A]] -⚬ Source[A] =
      rec { flatten =>
        from(
          onClose = close[Source[A]],
          onPoll  = poll[Source[A]] > either(
            Polled.empty[A],
            λ { case as |*| ass => poll(concatenate(carryOver)(as |*| flatten(ass))) }
          ),
        )
      }

    /** Emits the elements from each inner source, in order.
     *  Waits for each inner source to be fully closed before pulling/closing the next inner source.
     */
    def flattenStrict[A: Junction.Positive]: Source[Source[A]] -⚬ Source[A] =
      flatten[A](delayBy)

    /** Emits the elements from each inner source, in order.
     *  Does not wait for an inner source to be fully closed before pulling/closing the next inner source.
     */
    def flattenLax[A]: Source[Source[A]] -⚬ Source[A] =
      flatten[A](delayClosedBy)

    /** Alias for [[flattenStrict]].
     *  Waits for each inner source to be fully closed before pulling/closing the next inner source.
     */
    def flatten[A: Junction.Positive]: Source[Source[A]] -⚬ Source[A] =
      flattenStrict[A]

    /** Splits a stream of "`A` or `B`" to a stream of `A` and a stream of `B`.
      *
      * Polls the upstream only after ''both'' downstreams poll.
      * When either of the downstreams closes, the other downstream and the upstream are closed as well.
      */
    def partition[A, B]: Source[A |+| B] -⚬ (Source[A] |*| Source[B]) = rec { partition =>
      val fstClosed: Source[A |+| B] -⚬ (Done |*| Source[B]) =
        close[A |+| B] > introSnd(done > empty[B])

      val sndClosed: Source[A |+| B] -⚬ (Polled[A] |*| Done) =
        close[A |+| B] > introFst(done > Polled.empty[A])

      val bothPolled: Source[A |+| B] -⚬ (Polled[A] |*| Polled[B]) =
        λ { src =>
          poll(src) either {
            case Left(+(closed)) =>
              Polled.empty[A](closed) |*| Polled.empty[B](closed)
            case Right(h |*| t) =>
              val (ta |*| tb) = partition(t)
              h either {
                case Left(a)  => Polled.cons(a |*| ta) |*| poll(tb)
                case Right(b) => poll(ta) |*| Polled.cons(b |*| tb)
              }
          }
        }

      val fstPolled: Source[A |+| B] -⚬ (Polled[A] |*| Source[B]) =
        id                                     [                  Source[A |+| B]                   ]
          .>(choice(sndClosed, bothPolled)) .to[ (Polled[A] |*| Done) |&| (Polled[A] |*| Polled[B]) ]
          .>(coDistributeL)                 .to[  Polled[A] |*| (Done |&|                Polled[B]) ]
          .>(snd(fromChoice))               .to[  Polled[A] |*|    Source[B]                        ]

      id                                     [                  Source[A |+| B]                   ]
        .>(choice(fstClosed, fstPolled))  .to[ (Done |*| Source[B]) |&| (Polled[A] |*| Source[B]) ]
        .>(coDistributeR)                 .to[ (Done                |&| Polled[A]) |*| Source[B]  ]
        .>(fst(fromChoice))               .to[                     Source[A]       |*| Source[B]  ]
    }

    private def merge[A](continue: (Source[A] |*| Source[A]) -⚬ Source[A])(using
      A: Closeable[A],
    ): (Source[A] |*| Source[A]) -⚬ Source[A] = {
      def go: (Polled[A] |*| Source[A]) -⚬ Source[A] = {
        def goDownstream: (Polled[A] |*| Source[A]) -⚬ Source[A] = {
          def onClose: (Polled[A] |*| Source[A]) -⚬ Done =
            par(Polled.close(A.close), Source.close) > join

          def onPoll: (Polled[A] |*| Source[A]) -⚬ Polled[A] =
            λ { case as |*| bs =>
              ((as |*| poll(bs)) |> raceBy(notifyEither)) either {
                case Left(as |*| bs) => // `as` ready
                  as either {
                    case Left(closed) =>
                      Polled.delayClosedBy(closed |*| bs)
                    case Right(a |*| as) =>
                      Polled.cons(a |*| continue(as |*| Polled.unpoll(bs)))
                  }
                case Right(as |*| bs) => // `bs` ready
                  bs either {
                    case Left(closed) =>
                      Polled.delayClosedBy(closed |*| as)
                    case Right(b |*| bs) =>
                      Polled.cons(b |*| continue(Polled.unpoll(as) |*| bs))
                  }
              }
            }

          Source.from(onClose, onPoll)
        }

        def goPrefetched: ((A |*| Source[A]) |*| Source[A]) -⚬ Source[A] = {
          val onClose: ((A |*| Source[A]) |*| Source[A]) -⚬ Done =
            par(par(A.close, Source.close[A]) > join, Source.close[A]) > join
          val onPoll: ((A |*| Source[A]) |*| Source[A]) -⚬ Polled[A] =
            λ { case (a |*| as) |*| bs =>
              Polled.cons(a |*| continue(as |*| bs))
            }
          from(onClose, onPoll)
        }

        def go1: (Ping |*| (Polled[A] |*| Source[A])) -⚬ Source[A] =
          λ { case downstreamActing |*| (as |*| bs) =>
            (as |> notifyEither) match {
              case aReady |*| as =>
                ((downstreamActing |*| aReady) |> racePair) either {
                  case Left(?(_)) => // downstream acting
                    goDownstream(as |*| bs)
                  case Right(?(_)) => // `as` ready
                    as either {
                      case Left(closed) =>
                        Source.delayClosedBy(closed |*| bs)
                      case Right(a |*| as) =>
                        goPrefetched((a |*| as) |*| bs)
                    }
                }
            }
          }

        introFst(lInvertPongPing) > assocLR > snd(go1) > notifyAction
      }

      fst(poll) > go
    }

    /** Merges two [[Source]]s into one.
      * Left-biased: when upstreams are faster than the downstream, consistently favors the first one.
      * Prefetches up to 1 element from each of the upstream sources.
      * If downstream closes while there are prefetched elements,
      * they are discarded using the given [[Closeable]] instance.
      */
    def mergePreferred[A](using
      A: Closeable[A],
    ): (Source[A] |*| Source[A]) -⚬ Source[A] = rec { self =>
      merge(self)
    }


    /** Merges two [[Source]]s into one.
      * When upstreams are faster than the downstream, favors the one that emitted less recently.
      * Prefetches up to 1 element from each of the upstream sources.
      * If downstream closes while there are prefetched elements,
      * they are discarded using the given [[Closeable]] instance.
      */
    def mergeBalanced[A](using
      Closeable[A],
    ): (Source[A] |*| Source[A]) -⚬ Source[A] = rec { self =>
      merge(swap > self)
    }

    /** Merges two [[Source]]s into one. Alias for [[mergePreferred]]. */
    def merge[A](using Closeable[A]): (Source[A] |*| Source[A]) -⚬ Source[A] =
      mergePreferred

    def mergeEither[A, B](using Closeable[A], Closeable[B]): (Source[A] |*| Source[B]) -⚬ Source[A |+| B] =
      par(map(injectL), map(injectR)) > merge

    def mergeEitherPreferred[A, B](using Closeable[A], Closeable[B]): (Source[A] |*| Source[B]) -⚬ Source[A |+| B] =
      par(map(injectL), map(injectR)) > mergePreferred

    def mergeEitherBalanced[A, B](using Closeable[A], Closeable[B]): (Source[A] |*| Source[B]) -⚬ Source[A |+| B] =
      par(map(injectL), map(injectR)) > mergeBalanced

    /** Merges a list of [[Source]]s into a single [[Source]].
      * Head-biased: when upstreams are faster than the downstream,
      * consistently favors the upstreams from the beginning of the list.
      */
    def mergeAll[A](using
      Closeable[A],
    ): LList[Source[A]] -⚬ Source[A] =
      rec { self => λ { srcs =>
        switch( srcs )
          .is { case LList.Nil(u)         => Source.empty(done(u)) }
          .is { case LList.Cons(s |*| ss) => (s |*| self(ss)) |> merge }
          .end
      }}

    def prefetch[A](n: Int)(
      discardPrefetched: A -⚬ Done,
      tokenInvertor: Exists[[X] =>> Dual[LList[Done], X]] = Exists(listEndlessDuality[Done, Need](doneNeedDuality)),
    ): Source[A] -⚬ Source[A] = {
      type NegTokens = tokenInvertor.T
      val tokensDuality: Dual[LList[Done], NegTokens] = tokenInvertor.value

      λ { as =>
        val initialTokens: $[LList[Done]]  = LList.fill(n)(done)($.one)
        val (negTokens |*| returnedTokens) = tokensDuality.lInvert($.one)
        val tokens: $[LList[Done]]         = LList.concat(initialTokens |*| returnedTokens)
        val (shutdownPong |*| as1)         = Source.takeUntilPong(as)
        val (buffer |*| upstreamClosed) =
          takeForeach(tokens |*| as1) |> assocLR |> snd(joinMap(LList.fold, id))
        val bufferOut: $[Source[Done |*| A]] =
          buffer |> Source.fromLList(joinMap(id, discardPrefetched))
        val bufferedAs: $[Source[A]] =
          (bufferOut |> tapMap(swap)) match
            case (as |*| releasedTokens) =>
              as alsoElim (tokensDuality.rInvert(releasedTokens |*| negTokens))
        Source.notifyDownstreamClosed(
          shutdownPong |*|
          Source.delayClosedBy(upstreamClosed |*| bufferedAs)
        )
      }
    }

    /** Every element pulled from upstream is mapped using the given function
     *  and the right part of the resulting pair is output in the list.
     *  Note that if the resulting list is not consumed fast enough,
     *  elements will accumulate there without any bound.
     */
    def tapMap[A, B, W](f: A -⚬ (B |*| W)): Source[A] -⚬ (Source[B] |*| LList[W]) = rec { tapMap =>
      val onClose: Source[A] -⚬ (Done |*| LList[W]) =
        Source.close[A] > introSnd(LList.nil[W])

      val onPoll: Source[A] -⚬ (Polled[B] |*| LList[W]) =
        Source.poll[A] > either(
          Polled.empty[B] > introSnd(LList.nil[W]),
          λ { case a |*| as =>
            val b  |*| w  = f(a)
            val bs |*| ws = tapMap(as)
            Polled.cons(b |*| bs) |*| LList.cons(w |*| ws)
          },
        )

      choice(onClose, onPoll) > coDistributeR > fst(fromChoice)
    }

    def tap[A](using A: Cosemigroup[A]): Source[A] -⚬ (Source[A] |*| LList[A]) =
      tapMap(A.split)

    /** For each element of the input list, pull one element from the input source.
     *  If the input source runs out of elements before the input list does,
     *  the remaining elements of the input list are returned.
     */
    def takeForeach[X, A]: (LList[X] |*| Source[A]) -⚬ (LList[X |*| A] |*| LList[X] |*| Done) =
      rec { takeForeach =>
        λ { case (xs |*| as) =>
          LList.uncons(xs) either {
            case Left(*(unit)) =>
              LList.nil(unit) |*| LList.nil(unit) |*| Source.close(as)
            case Right(x |*| xs) =>
              Source.poll(as) either {
                case Left(done) =>
                  LList.nil($.one) |*| LList.cons(x |*| xs) |*| done
                case Right(a |*| as) =>
                  val (xas |*| leftovers |*| done) = takeForeach(xs |*| as)
                  LList.cons((x |*| a) |*| xas) |*| leftovers |*| done
              }
          }
        }
      }

    def takeUntilPong[A]: Source[A] -⚬ (Pong |*| Source[A]) = rec { takeUntilPong =>
      val onPong: Source[A] -⚬ (Pong |*| Source[A]) =
        Source.close[A] > Source.empty[A] > introFst(dismissPong)

      val onAction: Source[A] -⚬ (Pong |*| Source[A]) = {
        val onClose: Source[A] -⚬ (Pong |*| Done) =
          Source.close[A] > introFst(dismissPong)

        val onPoll: Source[A] -⚬ (Pong |*| Polled[A]) =
          Source.poll[A] > either(
            Polled.empty[A] > introFst(dismissPong),
            snd(takeUntilPong) > XI > snd(Polled.cons),
          )

        choice(onClose, onPoll) > coDistributeL > snd(fromChoice)
      }

      choice(onPong, onAction) > selectBy(forkPong, Source.notifyAction)
    }

    def terminateWith[A, T]: (Source[A] |*| Detained[T]) -⚬ SourceT[T, A] = rec { self =>
      val onClose: (Source[A] |*| Detained[T]) -⚬ T =
        λ { case as |*| t => t releaseWhen close(as) }

      val onPoll: (Source[A] |*| Detained[T]) -⚬ SourceT.Polled[T, A] =
        λ { case as |*| t =>
          poll(as) either {
            case Left(closed)    => SourceT.Polled.empty(t releaseWhen closed)
            case Right(a |*| as) => SourceT.Polled.cons(a |*| self(as |*| t))
          }
        }

      SourceT.from(onClose, onPoll)
    }

    given positiveJunction[A : Junction.Positive]: Junction.Positive[Source[A]] =
      Junction.Positive.from(Source.delayBy)

    given negativeSignaling[A]: Signaling.Negative[Source[A]] =
      Signaling.Negative.from(Source.notifyAction[A])

    given closeableSource[A]: Closeable[Source[A]] =
      Closeable.from(Source.close)

    object Polled {
      def close[A](neglect: A -⚬ Done): Polled[A] -⚬ Done =
        either(id, joinMap(neglect, Source.close))

      def empty[A]: Done -⚬ Polled[A] =
        injectL

      def cons[A]: (A |*| Source[A]) -⚬ Polled[A] =
        injectR

      def singleton[A]: (A |*| Done) -⚬ Polled[A] =
        snd(Source.empty[A]) > cons

      def switch[A, R](
        caseEmpty: Done -⚬ R,
        caseCons: (A |*| Source[A]) -⚬ R,
      ): Polled[A] -⚬ R = {
        either(caseEmpty, caseCons)
      }

      def unpoll[A](using A: Closeable[A]): Polled[A] -⚬ Source[A] =
        Source.from(close(A.close), id)

      def delayBy[A](using ev: Junction.Positive[A]): (Done |*| Polled[A]) -⚬ Polled[A] =
        id[Done |*| Polled[A]]          .to[  Done |*| (Done |+|           (A |*| Source[A])) ]
          ./>(distributeL)              .to[ (Done |*| Done) |+| (Done |*| (A |*| Source[A])) ]
          ./>.left(join)                .to[      Done       |+| (Done |*| (A |*| Source[A])) ]
          ./>.right(assocRL)            .to[      Done       |+| ((Done |*| A) |*| Source[A]) ]
          ./>.right.fst(ev.awaitPosFst) .to[      Done       |+| (          A  |*| Source[A]) ]

      def delayClosedBy_[A](
        delaySourceClosed: (Done |*| Source[A]) -⚬ Source[A],
      ): (Done |*| Polled[A]) -⚬ Polled[A] =
        id[Done |*| Polled[A]]                .to[  Done |*| (Done |+|           (A |*| Source[A])) ]
          ./>(distributeL)                    .to[ (Done |*| Done) |+| (Done |*| (A |*| Source[A])) ]
          ./>.left(join)                      .to[      Done       |+| (Done |*| (A |*| Source[A])) ]
          ./>.right(XI)                       .to[      Done       |+| (A |*| (Done |*| Source[A])) ]
          ./>.right.snd(delaySourceClosed)    .to[      Done       |+| (A |*|           Source[A] ) ]

      def delayClosedBy[A]: (Done |*| Polled[A]) -⚬ Polled[A] =
        delayClosedBy_(Source.delayClosedBy)

      def feedTo[A, B](
        f: (A |*| B) -⚬ PMaybe[B],
      ): (Polled[A] |*| B) -⚬ (Done |*| Maybe[B]) = rec { self =>
        val upstreamValue: ((A |*| Source[A]) |*| B) -⚬ (Done |*| Maybe[B]) = {
          val caseStop: (Source[A] |*| Done) -⚬ (Done |*| Maybe[B]) =
            joinMap(Source.close, id) > introSnd(Maybe.empty[B])
          val caseCont: (Source[A] |*| B) -⚬ (Done |*| Maybe[B]) =
            par(Source.poll, id) > self
          id                                             [ (     A    |*| Source[A]) |*| B  ]
            .>(fst(swap))                             .to[ (Source[A] |*|     A    ) |*| B  ]
            .>(assocLR)                               .to[  Source[A] |*| (   A      |*| B) ]
            .>(snd(f))                                .to[  Source[A] |*|        PMaybe[B]  ]
            .>(PMaybe.switchWithL(caseStop, caseCont)).to[         Done |*| Maybe[B]        ]
        }

        val upstreamClosed: (Done |*| B) -⚬ (Done |*| Maybe[B]) =
          par(id, Maybe.just)

        id[ (Done |+| (A |*| Source[A])) |*| B ]
          .>(distributeR)
          .>(either(upstreamClosed, upstreamValue))
      }
    }
  }

  private def rInvertLeaderF[R, S, T, U, A, B, x, y](
    rInvertR: (R |*| S) -⚬ One,
    rInvertU: (U |*| T) -⚬ One,
    rInvertB: (B |*| A) -⚬ One,
    rInvertSub: (y |*| x) -⚬ One,
  ): (StreamLeaderF[R, T, A, x] |*| StreamFollowerF[S, U, B, y]) -⚬ One =
    rInvertEither(
      rInvertR,
      swap > rInvertEither(
        rInvertU,
        rInvertPair(
          rInvertB,
          rInvertSub
        )
      )
    )

  def rInvertLeader[R, S, T, U, A, B](
    rInvertR: (R |*| S) -⚬ One,
    rInvertU: (U |*| T) -⚬ One,
    rInvertB: (B |*| A) -⚬ One,
  ): (StreamLeader[R, T, A] |*| StreamFollower[S, U, B]) -⚬ One =
    rInvertRec[StreamLeaderF[R, T, A, _], StreamFollowerF[S, U, B, _]](
      [X, Y] => (rInvertSub: (X |*| Y) -⚬ One) =>
        rInvertLeaderF(rInvertR, rInvertU, rInvertB, swap > rInvertSub)
    )

  private def lInvertFollowerF[R, S, T, U, A, B, x, y](
    lInvertR: One -⚬ (R |*| S),
    lInvertU: One -⚬ (U |*| T),
    lInvertB: One -⚬ (B |*| A),
    lInvertSub: One -⚬ (y |*| x),
  ): One -⚬ (StreamFollowerF[R, T, A, x] |*| StreamLeaderF[S, U, B, y]) =
    lInvertChoice(
      lInvertR,
      lInvertChoice(
        lInvertU,
        lInvertPair(
          lInvertB,
          lInvertSub
        )
      ) > swap
    )

  def lInvertFollower[R, S, T, U, A, B](
    lInvertR: One -⚬ (R |*| S),
    lInvertU: One -⚬ (U |*| T),
    lInvertB: One -⚬ (B |*| A),
  ): One -⚬ (StreamFollower[R, T, A] |*| StreamLeader[S, U, B]) =
    lInvertRec[StreamFollowerF[R, T, A, _], StreamLeaderF[S, U, B, _]](
      [X, Y] => (lInvertSub: One -⚬ (X |*| Y)) =>
        lInvertFollowerF(lInvertR, lInvertU, lInvertB, lInvertSub > swap)
    )

  given leaderFollowerDuality[R, S, T, U, A, B](using
    Dual[R, S],
    Dual[U, T],
    Dual[B, A],
  ): Dual[StreamLeader[R, T, A], StreamFollower[S, U, B]] with {
    override val rInvert: (StreamLeader[R, T, A] |*| StreamFollower[S, U, B]) -⚬ One =
      rInvertLeader(Dual[R, S].rInvert, Dual[U, T].rInvert, Dual[B, A].rInvert)

    override val lInvert: One -⚬ (StreamFollower[S, U, B] |*| StreamLeader[R, T, A]) =
      lInvertFollower[S, R, U, T, B, A](Dual[R, S].lInvert, Dual[U, T].lInvert, Dual[B, A].lInvert)
  }

  def rInvertStreamT[T, U, A, B](
    rInvertT: (T |*| U) -⚬ One,
    rInvertB: (B |*| A) -⚬ One,
  ): (StreamT[T, A] |*| SourceT[U, B]) -⚬ One =
    rInvertLeader[T, U, T, U, A, B](rInvertT, swap > rInvertT, rInvertB)

  def lInvertSourceT[T, U, A, B](
    lInvertT: One -⚬ (T |*| U),
    lInvertB: One -⚬ (B |*| A),
  ): One -⚬ (SourceT[T, A] |*| StreamT[U, B]) =
    lInvertFollower[T, U, T, U, A, B](lInvertT, lInvertT > swap, lInvertB)

  object Drain {
    type Pulling[A] = Need |&| (-[A] |*| Drain[A])

    def close[A]: Drain[A] -⚬ Need =
      StreamT.switch(id, chooseL)

    def closed[A]: Need -⚬ Drain[A] =
      StreamT.closed[Need, -[A]]

    def pulling[A]: Pulling[A] -⚬ Drain[A] =
      StreamT.next[Need, -[A]]

    def switch[A, R](
      onClose: Need -⚬ R,
      onPull: Pulling[A] -⚬ R,
    ): Drain[A] -⚬ R =
      StreamT.switch(onClose, onPull)

    def toEither[A]: Drain[A] -⚬ (Need |+| Pulling[A]) =
      StreamT.toEither

    def fromEither[A]: (Need |+| Pulling[A]) -⚬ Drain[A] =
      StreamT.fromEither

    def onCloseAwait[A]: (Done |*| Drain[A]) -⚬ Drain[A] = rec { self =>
      λ { case (d |*| drain) =>
        toEither(drain) either {
          case Left(closing) =>
            Drain.closed(needAbsorbDone(closing |*| d))
          case Right(pulling) =>
            Drain.pulling(Pulling.onCloseAwait0(self)(d |*| pulling))
        }
      }
    }

    object Pulling {
      def create[S, A](
        caseClose:    S -⚬ Need,
        caseWarrant:  S -⚬ (-[A] |*| Drain[A]),
      ): S -⚬ Pulling[A] =
        choice(caseClose, caseWarrant)

      def close[A]: Pulling[A] -⚬ Need =
        chooseL

      def warrant[A]: Pulling[A] -⚬ (-[A] |*| Drain[A]) =
        chooseR

      private[Drain] def onCloseAwait0[A](
        drainAwait: (Done |*| Drain[A]) -⚬ Drain[A],
      ): (Done |*| Pulling[A]) -⚬ Pulling[A] =
        create(
          caseClose   = λ { case (d |*| p) => needAbsorbDone(close(p) |*| d) },
          caseWarrant = snd(warrant) > XI > snd(drainAwait),
        )
    }

    private def needAbsorbDone: (Need |*| Done) -⚬ Need =
      fst(joinNeed) > assocLR > elimSnd(swap > rInvertSignal)
  }

  def rInvertDrain[A]: (Drain[A] |*| Source[A]) -⚬ One =
    rInvertStreamT[Need, Done, -[A], A](swap > rInvertSignal, backvert)

  def lInvertSource[A]: One -⚬ (Source[A] |*| Drain[A]) =
    lInvertSourceT(lInvertSignal > swap, forevert)

  def rInvertStream[A]: (Stream[A] |*| Sink[A]) -⚬ One =
    rInvertStreamT[Done, Need, A, -[A]](rInvertSignal, swap > backvert)

  def lInvertSink[A]: One -⚬ (Sink[A] |*| Stream[A]) =
    lInvertSourceT[Need, Done, -[A], A](lInvertSignal, forevert > swap)

  given drainSourceDuality[A]: Dual[Drain[A], Source[A]] with {
    override val rInvert: (Drain[A] |*| Source[A]) -⚬ One = rInvertDrain
    override val lInvert: One -⚬ (Source[A] |*| Drain[A]) = lInvertSource
  }

  given sourceDrainDuality[A]: Dual[Source[A], Drain[A]] =
    dualSymmetric(drainSourceDuality[A])

  given streamSinkDuality[A]: Dual[Stream[A], Sink[A]] with {
    override val rInvert = rInvertStream
    override val lInvert = lInvertSink
  }

  given sinkStreamDuality[A]: Dual[Sink[A], Stream[A]] =
    dualSymmetric(streamSinkDuality[A])
}
