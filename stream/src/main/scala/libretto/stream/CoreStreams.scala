package libretto.stream

import libretto.{CoreDSL, CoreLib}

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
  import dsl.$._
  import lib._

  type StreamLeaderF[T, A, X]   = T |+| (T |&| (A |*| X))
  type StreamFollowerF[T, A, X] = T |&| (T |+| (A |*| X))

  type StreamLeader[T, A]   = Rec[StreamLeaderF[T, A, _]]
  type StreamFollower[T, A] = Rec[StreamFollowerF[T, A, _]]

  opaque type Stream[A] = StreamLeader[Done, A]
  opaque type Source[A] = StreamFollower[Done, A]

  object StreamLeader {
    def pack[T, A]: StreamLeaderF[T, A, StreamLeader[T, A]] -⚬ StreamLeader[T, A] =
      dsl.pack

    def unpack[T, A]: StreamLeader[T, A] -⚬ StreamLeaderF[T, A, StreamLeader[T, A]] =
      dsl.unpack

    def closed[T, A]: T -⚬ StreamLeader[T, A] =
      injectL > pack

    def next[T, A]: (T |&| (A |*| StreamLeader[T, A])) -⚬ StreamLeader[T, A] =
      injectR > pack

    def switch[T, A, R](
      onClose: T -⚬ R,
      onNext: (T |&| (A |*| StreamLeader[T, A])) -⚬ R,
    ): StreamLeader[T, A] -⚬ R =
      unpack > either(onClose, onNext)
  }

  object Stream {
    def fromLeader[A]: StreamLeader[Done, A] -⚬ Stream[A] = id
    def toLeader[A]  : Stream[A] -⚬ StreamLeader[Done, A] = id
  }

  object Source {
    type Polled[A] = Done |+| (A |*| Source[A])

    def fromFollower[A]: StreamFollower[Done, A] -⚬ Source[A] = id
    def toFollower[A]  : Source[A] -⚬ StreamFollower[Done, A] = id

    def pack[A]: (Done |&| Polled[A]) -⚬ Source[A] =
      dsl.pack[StreamFollowerF[Done, A, _]]

    def unpack[A]: Source[A] -⚬ (Done |&| Polled[A]) =
      dsl.unpack[StreamFollowerF[Done, A, _]]

    def from[A, B](
      onClose: A -⚬ Done,
      onPoll: A -⚬ Polled[B],
    ): A -⚬ Source[B] =
      choice(onClose, onPoll) > pack

    def close[A]: Source[A] -⚬ Done =
      id                       [    Source[A]       ]
        .unpack             .to[ Done |&| Polled[A] ]
        .chooseL            .to[ Done               ]

    def poll[A]: Source[A] -⚬ Polled[A] =
      id                       [    Source[A]       ]
        .unpack             .to[ Done |&| Polled[A] ]
        .chooseR            .to[          Polled[A] ]

    def delayedPoll[A: Junction.Positive]: (Done |*| Source[A]) -⚬ Polled[A] =
      id                                       [ Done |*|     Source[A]        ]
        .>.snd(unpack)                      .to[ Done |*| (Done |&| Polled[A]) ]
        .>(chooseRWhenDone)                 .to[ Done |*|           Polled[A]  ]
        .>(Polled.delayBy[A])               .to[                    Polled[A]  ]

    /** Polls and discards all elements. */
    def drain[A](implicit A: PComonoid[A]): Source[A] -⚬ Done =
      rec { self =>
        poll[A] > either(id, joinMap(A.counit, self))
      }

    private def emptyF[A]: Done -⚬ StreamFollowerF[Done, A, Source[A]] =
      choice[Done, Done, Polled[A]](id, injectL)

    def empty[A]: Done -⚬ Source[A] =
      emptyF[A].pack

    def cons[A](implicit A: PAffine[A]): (A |*| Source[A]) -⚬ Source[A] = {
      val onClose: (A |*| Source[A]) -⚬ Done      = joinMap(A.neglect, Source.close)
      val onPoll:  (A |*| Source[A]) -⚬ Polled[A] = Polled.cons
      from(onClose, onPoll)
    }

    def fromLList[A](implicit A: PAffine[A]): LList[A] -⚬ Source[A] = rec { self =>
      LList.switch(
        caseNil  = done          > Source.empty[A],
        caseCons = par(id, self) > Source.cons[A],
      )
    }

    def of[A](as: (One -⚬ A)*)(implicit A: PAffine[A]): One -⚬ Source[A] =
      LList.of(as: _*) > fromLList

    def repeatedly[A](f: Done -⚬ A): Done -⚬ Source[A] = rec { self =>
      from(
        onClose = id[Done],
        onPoll = forkMap(f, self) > Polled.cons,
      )
    }

    /** Signals the first action (i.e. [[poll]] or [[close]]) via a negative ([[Pong]]) signal. */
    def notifyAction[A]: (Pong |*| Source[A]) -⚬ Source[A] =
      id                                     [             Source[A]         ]
        .<(pack)                        .from[           Done |&| Polled[A]  ]
        .<(notifyChoice)                .from[ Pong |*| (Done |&| Polled[A]) ]
        .<(par(id, unpack))             .from[ Pong |*|    Source[A]         ]

    /** Delays the first action ([[poll]] or [[close]]) until the [[Done]] signal completes. */
    def delayBy[A](implicit ev: Junction.Positive[A]): (Done |*| Source[A]) -⚬ Source[A] =
      id                                           [  Done |*|      Source[A]                  ]
        .>.snd(unpack)                          .to[  Done |*| (Done  |&|           Polled[A]) ]
        .>(delayChoiceUntilDone)                .to[ (Done |*|  Done) |&| (Done |*| Polled[A]) ]
        .bimap(join, Polled.delayBy[A])         .to[       Done       |&|           Polled[A]  ]
        .pack[StreamFollowerF[Done, A, *]]      .to[               Source[A]                   ]

    def delayable[A](using Junction.Positive[A]): Source[A] -⚬ (Need |*| Source[A]) =
      λ { src =>
        val (n |*| d) = one > lInvertSignal
        n |*| ((d |*| src) > delayBy)
      }

    /** Delays the final [[Done]] signal (signaling end of stream or completed [[close]]) until the given [[Done]]
      * signal completes.
      */
    def delayClosedBy[A]: (Done |*| Source[A]) -⚬ Source[A] = rec { self =>
      id                                               [  Done |*|      Source[A]                  ]
        .>.snd(unpack)                              .to[  Done |*| (Done  |&|           Polled[A]) ]
        .>(coFactorL)                               .to[ (Done |*|  Done) |&| (Done |*| Polled[A]) ]
        .bimap(join, Polled.delayClosedBy(self))   .to[       Done        |&|           Polled[A]  ]
        .pack[StreamFollowerF[Done, A, *]]          .to[               Source[A]                   ]
    }

    /** Blocks the first action ([[poll]] or [[close]]) on this [[Source]] until released. */
    def detain[A: Junction.Positive]: Source[A] -⚬ Detained[Source[A]] =
      Detained(delayBy)

    /** Delays the final [[Done]] signal resulting from [[close]] or end of stream. */
    def detainClosed[A]: Source[A] -⚬ Detained[Source[A]] =
      Detained(delayClosedBy)

    def map[A, B](f: A -⚬ B): Source[A] -⚬ Source[B] = rec { self =>
      from(close[A], poll[A].>.right(par(f, self)))
    }

    def forEachSequentially[A: Junction.Positive](f: A -⚬ Done): Source[A] -⚬ Done = rec { self =>
      val caseCons: (A |*| Source[A]) -⚬ Done =
        par(f, id) > Source.delayBy[A] > self

      poll[A] > Polled.switch(caseEmpty = id[Done], caseCons)
    }

    /** The second [[Source]] is "detained" because that gives the client flexibility in how the [[Done]] signal resulting from
      * the exhaustion of the first [[Source]] is awaited. For example, if polling of the second [[Source]]
      * should be delayed until the first [[Source]] is completely shut down, the client can use [[detain]] to delay the
      * second [[Source]]. If polling of the second [[Source]] should start as soon as it is known that there are
      * no more elements in the first [[Source]], the client can use [[detainClosed]] to delay the second [[Source]]
      * (this latter behavior is the behavior of [[concat]]).
      */
    def concatenate[A]: (Source[A] |*| Detained[Source[A]]) -⚬ Source[A] = rec { self =>
      val onClose: (Source[A] |*| Detained[Source[A]]) -⚬ Done =
        joinMap(Source.close, Detained.releaseAsap > Source.close)

      val onPoll: (Source[A] |*| Detained[Source[A]]) -⚬ Polled[A] =
        λ { case src1 |*| detainedSrc2 =>
          poll(src1) switch {
            case Left(src1Closed) =>
              val src2 = Detained.releaseBy(src1Closed |*| detainedSrc2)
              poll(src2)
            case Right(a |*| as) =>
              Polled.cons(a |*| self(as |*| detainedSrc2))
          }
        }

      from(onClose, onPoll)
    }

    def concat[A]: (Source[A] |*| Source[A]) -⚬ Source[A] =
      id.>.snd(detainClosed) > concatenate

    /** Splits a stream of "`A` or `B`" to a stream of `A` and a stream of `B`.
      *
      * Polls the upstream only after ''both'' downstreams poll.
      * When either of the downstreams closes, the other downstream and the upstream are closed as well.
      */
    def partition[A, B]: Source[A |+| B] -⚬ (Source[A] |*| Source[B]) = rec { partition =>
      val fstClosed: Source[A |+| B] -⚬ (Done |*| Source[B]) =
        close[A |+| B].introSnd(done > empty[B])

      val sndClosed: Source[A |+| B] -⚬ (Polled[A] |*| Done) =
        close[A |+| B].introFst(done > Polled.empty[A])

      val bothPolled: Source[A |+| B] -⚬ (Polled[A] |*| Polled[B]) =
        λ { src =>
          poll(src) switch {
            case Left(+(closed)) =>
              Polled.empty[A](closed) |*| Polled.empty[B](closed)
            case Right(h |*| t) =>
              val (ta |*| tb) = partition(t)
              h switch {
                case Left(a)  => Polled.cons(a |*| ta) |*| poll(tb)
                case Right(b) => poll(ta) |*| Polled.cons(b |*| tb)
              }
          }
        }

      val fstPolled: Source[A |+| B] -⚬ (Polled[A] |*| Source[B]) =
        id                                   [                  Source[A |+| B]                   ]
          .choice(sndClosed, bothPolled)  .to[ (Polled[A] |*| Done) |&| (Polled[A] |*| Polled[B]) ]
          .coDistributeL                  .to[  Polled[A] |*| (Done |&|                Polled[B]) ]
          .>.snd(pack)                    .to[  Polled[A] |*|    Source[B]                        ]

      id                                 [                  Source[A |+| B]                   ]
        .choice(fstClosed, fstPolled) .to[ (Done |*| Source[B]) |&| (Polled[A] |*| Source[B]) ]
        .coDistributeR                .to[ (Done                |&| Polled[A]) |*| Source[B]  ]
        .>.fst(pack)                  .to[                     Source[A]       |*| Source[B]  ]
    }

    /** Merges two [[Source]]s into one.
      * Left-biased: when there is a value available from both upstreams, favors the first one.
      */
    def merge[A](implicit
      A1: Junction.Positive[A],
      A2: PAffine[A],
    ): (Source[A] |*| Source[A]) -⚬ Source[A] = rec { self =>
      val onClose: (Source[A] |*| Source[A]) -⚬ Done      = joinMap(close, close)
      val onPoll : (Source[A] |*| Source[A]) -⚬ Polled[A] = par(poll, poll) > Polled.merge(self)
      from(onClose, onPoll)
    }

    /** Merges a list of [[Source]]s into a single [[Source]].
      * Head-biased: when there is an element available from multiple upstreams, favors the upstream closest to the
      * head of the input list.
      */
    def mergeAll[A](implicit
      A1: Junction.Positive[A],
      A2: PAffine[A],
    ): LList[Source[A]] -⚬ Source[A] =
      rec { self =>
        LList.switch(
          caseNil = done > Source.empty,
          caseCons = par(id, self) > merge,
        )
      }

    implicit def positiveJunction[A](implicit A: Junction.Positive[A]): Junction.Positive[Source[A]] =
      Junction.Positive.from(Source.delayBy)

    implicit def negativeSignaling[A]: Signaling.Negative[Source[A]] =
      Signaling.Negative.from(Source.notifyAction[A])

    implicit def negativeSource[A](implicit A: Junction.Positive[A]): SignalingJunction.Negative[Source[A]] =
      SignalingJunction.Negative.from(
        negativeSignaling,
        Junction.invert(positiveJunction),
      )

    implicit def pAffineSource[A]: PAffine[Source[A]] =
      PAffine.from(Source.close)

    object Polled {
      def close[A](neglect: A -⚬ Done): Polled[A] -⚬ Done =
        either(id, joinMap(neglect, Source.close))

      def empty[A]: Done -⚬ Polled[A] =
        injectL

      def cons[A]: (A |*| Source[A]) -⚬ Polled[A] =
        injectR

      def switch[A, R](
        caseEmpty: Done -⚬ R,
        caseCons: (A |*| Source[A]) -⚬ R,
      ): Polled[A] -⚬ R = {
        either(caseEmpty, caseCons)
      }

      def unpoll[A](implicit A: PAffine[A]): Polled[A] -⚬ Source[A] =
        Source.from(close(A.neglect), id)

      def delayBy[A](implicit ev: Junction.Positive[A]): (Done |*| Polled[A]) -⚬ Polled[A] =
        id[Done |*| Polled[A]]          .to[  Done |*| (Done |+|           (A |*| Source[A])) ]
          .distributeL                  .to[ (Done |*| Done) |+| (Done |*| (A |*| Source[A])) ]
          .>.left(join)                 .to[      Done       |+| (Done |*| (A |*| Source[A])) ]
          .>.right(assocRL)             .to[      Done       |+| ((Done |*| A) |*| Source[A]) ]
          .>.right.fst(ev.awaitPosFst)  .to[      Done       |+| (          A  |*| Source[A]) ]

      def delayClosedBy[A](
        delaySourceClosed: (Done |*| Source[A]) -⚬ Source[A],
      ): (Done |*| Polled[A]) -⚬ Polled[A] =
        id[Done |*| Polled[A]]                .to[  Done |*| (Done |+|           (A |*| Source[A])) ]
          .distributeL                        .to[ (Done |*| Done) |+| (Done |*| (A |*| Source[A])) ]
          .>.left(join)                       .to[      Done       |+| (Done |*| (A |*| Source[A])) ]
          .>.right(XI)                        .to[      Done       |+| (A |*| (Done |*| Source[A])) ]
          .>.right.snd(delaySourceClosed)     .to[      Done       |+| (A |*|           Source[A] ) ]

      def feedTo[A, B](
        f: (A |*| B) -⚬ PMaybe[B],
      ): (Polled[A] |*| B) -⚬ (Done |*| Maybe[B]) = rec { self =>
        val upstreamValue: ((A |*| Source[A]) |*| B) -⚬ (Done |*| Maybe[B]) = {
          val caseStop: (Source[A] |*| Done) -⚬ (Done |*| Maybe[B]) =
            joinMap(Source.close, id) > introSnd(Maybe.empty[B])
          val caseCont: (Source[A] |*| B) -⚬ (Done |*| Maybe[B]) =
            par(Source.poll, id) > self
          id                                             [ (     A    |*| Source[A]) |*| B  ]
            .>.fst(swap)                              .to[ (Source[A] |*|     A    ) |*| B  ]
            .assocLR                                  .to[  Source[A] |*| (   A      |*| B) ]
            .>.snd(f)                                 .to[  Source[A] |*|        PMaybe[B]  ]
            .>(PMaybe.switchWithL(caseStop, caseCont)).to[         Done |*| Maybe[B]        ]
        }

        val upstreamClosed: (Done |*| B) -⚬ (Done |*| Maybe[B]) =
          par(id, Maybe.just)

        id[ (Done |+| (A |*| Source[A])) |*| B ]
          .distributeR
          .either(upstreamClosed, upstreamValue)
      }

      implicit def positivePolled[A](implicit A: Junction.Positive[A]): SignalingJunction.Positive[Polled[A]] =
        SignalingJunction.Positive.eitherPos(
          SignalingJunction.Positive.signalingJunctionPositiveDone,
          Junction.Positive.byFst(A),
        )

      /** Merges two [[Polled]]s into one.
        * Left-biased: whenever there is a value available from both upstreams, favors the first one.
        *
        * @param mergeSources left-biased merge of two [[Source]]s.
        */
      def merge[A](
        mergeSources: (Source[A] |*| Source[A]) -⚬ Source[A],
      )(implicit
        A1: Junction.Positive[A],
        A2: PAffine[A],
      ): (Polled[A] |*| Polled[A]) -⚬ Polled[A] = {
        // checks the first argument first, uses the given function for recursive calls
        def go(merge: (Source[A] |*| Source[A]) -⚬ Source[A]): (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
          id[Polled[A] |*| Polled[A]]   .to[ (Done                |+|  (A |*| Source[A])) |*| Polled[A]   ]
            .distributeR                .to[ (Done |*| Polled[A]) |+| ((A |*| Source[A])  |*| Polled[A] ) ]
            .>.left(delayBy[A])         .to[           Polled[A]  |+| ((A |*| Source[A])  |*| Polled[A] ) ]
            .>.right.snd(unpoll)        .to[           Polled[A]  |+| ((A |*| Source[A])  |*| Source[A] ) ]
            .>.right.assocLR            .to[           Polled[A]  |+| ( A |*| (Source[A]  |*| Source[A])) ]
            .>.right.snd(merge)         .to[           Polled[A]  |+| ( A |*|           Source[A]       ) ]
            .>.right(cons)              .to[           Polled[A]  |+|     Polled[A]                       ]
            .either(id, id)             .to[                   Polled[A]                                  ]

        // checks the first argument first
        val goFst: (Polled[A] |*| Polled[A]) -⚬ Polled[A] = go(mergeSources)

        // checks the second argument first
        val goSnd: (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
          swap > go(swap > mergeSources)

        raceSwitch(goFst, goSnd)
      }
    }
  }

  private def rInvertLeaderF[T, U, A, B, x, y](
    rInvertT: (T |*| U) -⚬ One,
    rInvertA: (A |*| B) -⚬ One,
    rInvertSub: (x |*| y) -⚬ One,
  ): (StreamLeaderF[T, A, x] |*| StreamFollowerF[U, B, y]) -⚬ One =
    rInvertEither(
      rInvertT,
      swap > rInvertEither(
        swap > rInvertT,
        swap > rInvertPair(
          rInvertA,
          rInvertSub
        )
      )
    )

  def rInvertLeader[T, U, A, B](
    rInvertT: (T |*| U) -⚬ One,
    rInvertElem: (A |*| B) -⚬ One,
  ): (StreamLeader[T, A] |*| StreamFollower[U, B]) -⚬ One =
    rInvertRec[StreamLeaderF[T, A, _], StreamFollowerF[U, B, _]](
      [X, Y] => (rInvertSub: (X |*| Y) -⚬ One) =>
        rInvertLeaderF(rInvertT, rInvertElem, rInvertSub)
    )

  private def lInvertFollowerF[T, U, A, B, x, y](
    lInvertT: One -⚬ (T |*| U),
    lInvertA: One -⚬ (A |*| B),
    lInvertSub: One -⚬ (x |*| y),
  ): One -⚬ (StreamFollowerF[T, A, x] |*| StreamLeaderF[U, B, y]) =
    lInvertChoice(
      lInvertT,
      lInvertChoice(
        lInvertT > swap,
        lInvertPair(
          lInvertA,
          lInvertSub
        ) > swap
      ) > swap
    )

  def lInvertFollower[T, U, A, B](
    lInvertT: One -⚬ (T |*| U),
    lInvertElem: One -⚬ (A |*| B),
  ): One -⚬ (StreamFollower[T, A] |*| StreamLeader[U, B]) =
    lInvertRec[StreamFollowerF[T, A, _], StreamLeaderF[U, B, _]](
      [X, Y] => (lInvertSub: One -⚬ (X |*| Y)) =>
        lInvertFollowerF(lInvertT, lInvertElem, lInvertSub)
    )

  given leaderFollowerDuality[T, U, A, B](using
    Dual[T, U],
    Dual[A, B],
  ): Dual[StreamLeader[T, A], StreamFollower[U, B]] with {
    override val rInvert: (StreamLeader[T, A] |*| StreamFollower[U, B]) -⚬ One =
      rInvertLeader(Dual[T, U].rInvert, Dual[A, B].rInvert)

    override val lInvert: One -⚬ (StreamFollower[U, B] |*| StreamLeader[T, A]) =
      lInvertFollower[U, T, B, A](Dual[T, U].lInvert, Dual[A, B].lInvert)
  }

  @deprecated("Renamed to Source")
  type LPollable[A] = Source[A]

  @deprecated("Renamed to Source")
  val LPollable: Source.type = Source
}
