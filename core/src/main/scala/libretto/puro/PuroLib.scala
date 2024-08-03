package libretto.puro

import libretto.cats.{Bifunctor, Comonad, ContraFunctor, Functor, Monad}
import libretto.lambda.{Category, Extractor, SymmetricMonoidalCategory}
import libretto.lambda.util.SourcePos
import libretto.lambda.util.unapply.*
import libretto.util.{Equal, ∀}
import scala.annotation.tailrec
import scala.collection.immutable.{:: as NonEmptyList}

object PuroLib {
  def apply(dsl: Puro): PuroLib[dsl.type] =
    new PuroLib(dsl)
}

class PuroLib[DSL <: Puro](val dsl: DSL) { lib =>
  import dsl.*

  /** Evidence that `A` flowing in one direction is equivalent to to `B` flowing in the opposite direction.
    * It must hold that
    * ```
    *         ┏━━━━━┓                         ┏━━━━━┓
    *         ┞─┐ r ┃                         ┃  l  ┞─┐
    *         ╎A│ I ┃                         ┃  I  ╎B│
    *         ┟─┘ n ┃                         ┃  n  ┟─┘
    *   ┏━━━━━┫   v ┃     ┏━━━━━━━━━┓         ┃  v  ┣━━━━━┓     ┏━━━━━━━━━┓
    *   ┃  l  ┞─┐ e ┃     ┞─┐       ┞─┐       ┃  e  ┞─┐ r ┃     ┞─┐       ┞─┐
    *   ┃  I  ╎B│ r ┃  =  ╎A│ id[A] ╎A│       ┃  r  ╎A│ I ┃  =  ╎B│ id[B] ╎B│
    *   ┃  n  ┟─┘ t ┃     ┟─┘       ┟─┘       ┃  t  ┟─┘ n ┃     ┟─┘       ┟─┘
    *   ┃  v  ┣━━━━━┛     ┗━━━━━━━━━┛         ┗━━━━━┫   v ┃     ┗━━━━━━━━━┛
    *   ┃  e  ┞─┐                                   ┞─┐ e ┃
    *   ┃  r  ╎A│                                   ╎B│ r ┃
    *   ┃  t  ┟─┘                                   ┟─┘ t ┃
    *   ┗━━━━━┛                                     ┗━━━━━┛
    * ```
    */
  trait Dual[A, B] {
    /** Reverses the input that flows along the `-⚬` arrow (say it is the `A` input) to its dual (`B`) flowing
      * against the direction of the arrow.
      *
      * ```
      *   ┏━━━━━━━┓
      *   ┞─┐   r ┃
      *   ╎A│─┐ I ┃
      *   ┟─┘ ┆ n ┃
      *   ┃   ┆ v ┃
      *   ┞─┐ ┆ e ┃
      *   ╎B│←┘ r ┃
      *   ┟─┘   t ┃
      *   ┗━━━━━━━┛
      * ```
      */
    val rInvert: (A |*| B) -⚬ One

    /** Reverses the output that flows against the `-⚬` arrow (say it is the `B` output) to its dual (`A`) flowing
      * in the direction of the arrow.
      *
      * ```
      *   ┏━━━━━┓
      *   ┃ l   ┞─┐
      *   ┃ I ┌─╎B│
      *   ┃ n ┆ ┟─┘
      *   ┃ v ┆ ┃
      *   ┃ e ┆ ┞─┐
      *   ┃ r └→╎A│
      *   ┃ t   ┟─┘
      *   ┗━━━━━┛
      * ```
      */
    val lInvert: One -⚬ (B |*| A)

    /** Law stating that [[rInvert]] followed by [[lInvert]] is identity. */
    def law_rl_id: Equal[A -⚬ A] =
      Equal(
        id[A]                   .to[ A               ]
          .>(introSnd(lInvert)) .to[ A |*| (B |*| A) ]
          .>(assocRL)           .to[ (A |*| B) |*| A ]
          .>(elimFst(rInvert))  .to[               A ],
        id[A]
      )

    /** Law stating that [[lInvert]] followed by [[rInvert]] is identity. */
    def law_lr_id: Equal[B -⚬ B] =
      Equal(
        id[B]                   .to[               B ]
          .>(introFst(lInvert)) .to[ (B |*| A) |*| B ]
          .>(assocLR)           .to[ B |*| (A |*| B) ]
          .>(elimSnd(rInvert))  .to[ B               ],
        id[B]
      )
  }

  object Dual {
    /** Convenience method to summon instances of [[dsl.Dual]]. */
    def apply[A, B](using ev: Dual[A, B]): Dual[A, B] = ev
  }

  def rInvert[A, B](using ev: Dual[A, B]): (A |*| B) -⚬ One =
    ev.rInvert

  def lInvert[A, B](using ev: Dual[A, B]): One -⚬ (B |*| A) =
    ev.lInvert

  type Functor[F[_]] =
    libretto.cats.Functor[-⚬, F]

  object Functor {
    def apply[F[_]: Functor]: Functor[F] =
      libretto.cats.Functor[-⚬, F]
  }

  type ContraFunctor[F[_]] =
    libretto.cats.ContraFunctor[-⚬, F]

  object ContraFunctor {
    def apply[F[_]: ContraFunctor]: ContraFunctor[F] =
      libretto.cats.ContraFunctor[-⚬, F]
  }

  type Bifunctor[F[_, _]] =
    libretto.cats.Bifunctor[-⚬, F]

  object Bifunctor {
    def apply[F[_, _]: Bifunctor]: Bifunctor[F] =
      libretto.cats.Bifunctor[-⚬, F]
  }

  /** Functor from category [[-⚬]] to the category `=>` of Scala functions.
    * It takes a morphism `A -⚬ B` internal to the DSL and maps it to a morphism `F[A] => F[B]` in the meta language
    * (Scala), i.e. external to the DSL.
    */
  trait Externalizer[F[_]] { self =>
    def lift[A, B](f: A -⚬ B): F[A] => F[B]

    def ∘[G[_]](that: Functor[G]): Externalizer[[x] =>> F[G[x]]] =
      new Externalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[A]] => F[G[B]] =
          self.lift(that.lift(f))
      }

    def ∘[G[_]](that: ContraFunctor[G]): ContraExternalizer[[x] =>> F[G[x]]] =
      new ContraExternalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[B]] => F[G[A]] =
          self.lift(that.lift(f))
      }

    def ∘[G[_, _]](that: Bifunctor[G]): BiExternalizer[[x, y] =>> F[G[x, y]]] =
      new BiExternalizer[[x, y] =>> F[G[x, y]]] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): F[G[A, C]] => F[G[B, D]] =
          self.lift(that.lift(f, g))
      }
  }

  object Externalizer {
    given outportFrom[A]: Externalizer[[x] =>> A -⚬ x] with {
      override def lift[B, C](f: B -⚬ C): (A -⚬ B) => (A -⚬ C) =
        dsl.andThen(_, f)
    }
  }

  trait BiExternalizer[F[_, _]] { self =>
    def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): F[A, C] => F[B, D]

    def fst[B]: Externalizer[F[*, B]] =
      new Externalizer[F[*, B]] {
        def lift[A1, A2](f: A1 -⚬ A2): F[A1, B] => F[A2, B] =
          self.lift(f, id)
      }

    def snd[A]: Externalizer[F[A, *]] =
      new Externalizer[F[A, *]] {
        def lift[B1, B2](g: B1 -⚬ B2): F[A, B1] => F[A, B2] =
          self.lift(id, g)
      }
  }

  /** Contravariant functor from category [[-⚬]] to the category `=>` of Scala functions.
    * It takes a morphism `A -⚬ B` internal to the DSL and maps it to a morphism `F[B] => F[A]` in the meta language
    * (Scala), i.e. external to the DSL.
    */
  trait ContraExternalizer[F[_]] { self =>
    def lift[A, B](f: A -⚬ B): F[B] => F[A]

    def ∘[G[_]](that: Functor[G]): ContraExternalizer[[x] =>> F[G[x]]] =
      new ContraExternalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[B]] => F[G[A]] =
          self.lift(that.lift(f))
      }

    def ∘[G[_]](that: ContraFunctor[G]): Externalizer[[x] =>> F[G[x]]] =
      new Externalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[A]] => F[G[B]] =
          self.lift(that.lift(f))
      }
  }

  object ContraExternalizer {
    given inportTo[C]: ContraExternalizer[[x] =>> x -⚬ C] with {
      def lift[A, B](f: A -⚬ B): (B -⚬ C) => (A -⚬ C) =
        f > _
    }
  }

  /** Expresses the intent that interaction with `A` is (at least partially) obstructed.
    * The detention can be ended by receiving a signal.
    *
    * Note that whether/how much the interaction with `Detained[A]` is actually
    * obstructed is completely up to the producer of `Detained[A]`.
    *
    * Equivalent to `Need |*| A` (or `Done =⚬ A` if the DSL extends [[ClosedDSL]]).
    */
  opaque type Detained[A] = Need |*| A
  object Detained {
    def untilNeed[A, B](f: A -⚬ (Need |*| B)): A -⚬ Detained[B] =
      f

    def untilDone[A, B](f: (Done |*| A) -⚬ B): A -⚬ Detained[B] =
      id[A] > introFst(lInvertSignal) > assocLR > snd(f)

    def apply[A, B](f: (Done |*| A) -⚬ B): A -⚬ Detained[B] =
      Detained.untilDone(f)

    def thunk[A](f: Done -⚬ A): One -⚬ Detained[A] =
      lInvertSignal > snd(f)

    /** Present the first part of a [[Detained]] pair as non-detained. */
    def excludeFst[A, B]: Detained[A |*| B] -⚬ (A |*| Detained[B]) =
      XI

    /** Present the second part of a [[Detained]] pair as non-detained. */
    def excludeSnd[A, B]: Detained[A |*| B] -⚬ (Detained[A] |*| B) =
      assocRL

    def releaseBy[A]: (Done |*| Detained[A]) -⚬ A =
      assocRL > elimFst(rInvertSignal)

    def releaseAsap[A]: Detained[A] -⚬ A =
      elimFst(need)

    /** Subsequent [[releaseBy]] won't have effect until also the given [[Need]] signal arrives. */
    def extendDetentionUntilNeed[A]: Detained[A] -⚬ (Need |*| Detained[A]) =
      fst(joinNeed) > assocLR

    /** Subsequent [[releaseBy]] won't have effect until also the given [[Done]] signal arrives. */
    def extendDetentionUntil[A]: (Done |*| Detained[A]) -⚬ Detained[A] =
      snd(extendDetentionUntilNeed) > assocRL > elimFst(rInvertSignal)

    def notifyReleaseNeg[A]: (Pong |*| Detained[A]) -⚬ Detained[A] =
      assocRL > fst(notifyNeedL)

    def notifyReleasePos[A]: Detained[A] -⚬ (Ping |*| Detained[A]) =
      introFst(lInvertPongPing > swap) > assocLR > snd(notifyReleaseNeg)

    /** Signals when it is released, awaiting delays the release. */
    given [A]: SignalingJunction.Negative[Detained[A]] =
      SignalingJunction.Negative.byFst

    given Transportive[Detained] with {
      override val category: Category[-⚬] =
        dsl.category

      override def lift[A, B](f: A -⚬ B): Detained[A] -⚬ Detained[B] =
        snd(f)

      override def inL[A, B]: (A |*| Detained[B]) -⚬ Detained[A |*| B] =
        XI

      override def outL[A, B]: Detained[A |*| B] -⚬ (A |*| Detained[B]) =
        XI
    }
  }

  extension [A](a: $[Detained[A]]) {
    def releaseWhen(trigger: $[Done])(using LambdaContext): $[A] =
      Detained.releaseBy(trigger |*| a)
  }

  /** Like [[Detained]], expresses that interaction with `A` is (at least partially) obstructed,
    * but does not have the ability to absorb a non-dismissible signal (namely [[Done]])—the signal
    * to resume must be dismissible (namely [[Ping]]).
    */
  opaque type Deferred[A] = Pong |*| A
  object Deferred {
    def untilPong[A, B](f: A -⚬ (Pong |*| B)): A -⚬ Deferred[B] =
      f

    def untilPing[A, B](f: (Ping |*| A) -⚬ B): A -⚬ Deferred[B] =
      id[A] > introFst(lInvertPongPing) > assocLR > snd(f)

    def apply[A, B](f: (Ping |*| A) -⚬ B): A -⚬ Deferred[B] =
      Deferred.untilPing(f)

    def thunk[A](f: Ping -⚬ A): One -⚬ Deferred[A] =
      lInvertPongPing > snd(f)

    def resumeBy[A]: (Ping |*| Deferred[A]) -⚬ A =
      assocRL > elimFst(rInvertPingPong)

    def forceResume[A]: Deferred[A] -⚬ A =
      elimFst(pong)

    def notifyResumeNeg[A]: (Pong |*| Deferred[A]) -⚬ Deferred[A] =
      assocRL > fst(forkPong)

    def notifyResumePos[A]: Deferred[A] -⚬ (Ping |*| Deferred[A]) =
      introFst(lInvertPongPing > swap) > assocLR > snd(notifyResumeNeg)

    /** Signals resumption. */
    given signalingDeferred[A]: Signaling.Negative[Deferred[A]] =
      Signaling.Negative.byFst

    /** Defers resumption. */
    given deferrableDeferred[A]: Deferrable.Negative[Deferred[A]] =
      Deferrable.Negative.byFst
  }

  extension [A](a: $[Deferred[A]]) {
    def resumeWhen(trigger: $[Ping])(using LambdaContext): $[A] =
      Deferred.resumeBy(trigger |*| a)
  }

  object Deferrable {
    /** Represents ''a'' way how (part of) `A` can be deferred until a [[Ping]]. */
    trait Positive[A] {
      def awaitPingFst: (Ping |*| A) -⚬ A

      def awaitPingSnd: (A |*| Ping) -⚬ A =
        swap > awaitPingFst

      /** Alias for [[awaitPingFst]]. */
      def awaitPing: (Ping |*| A) -⚬ A =
        awaitPingFst

      def defer: A -⚬ Deferred[A] =
        Deferred.untilPing(awaitPingFst)

      def law_awaitPingIdentity: Equal[(One |*| A) -⚬ A] =
        Equal(
          fst(ping) > awaitPingFst,
          elimFst,
        )

      def law_awaitPingComposition: Equal[(Ping |*| (Ping |*| A)) -⚬ A] =
        Equal(
          snd(awaitPingFst) > awaitPingFst,
          assocRL > fst(joinPing) > awaitPingFst,
        )
    }

    /** Represents ''a'' way how (part of) `A` can be deferred until a [[Pong]]. */
    trait Negative[A] {
      def awaitPongFst: A -⚬ (Pong |*| A)

      def awaitPongSnd: A -⚬ (A |*| Pong) =
        awaitPongFst > swap

      /** Alias for [[awaitPongFst]]. */
      def awaitPong: A -⚬ (Pong |*| A) =
        awaitPongFst

      def defer: A -⚬ Deferred[A] =
        Deferred.untilPong(awaitPongFst)

      def law_awaitPongIdentity: Equal[A -⚬ (One |*| A)] =
        Equal(
          awaitPongFst > fst(pong),
          introFst,
        )

      def law_awaitPongComposition: Equal[A -⚬ (Pong |*| (Pong |*| A))] =
        Equal(
          awaitPongFst > snd(awaitPongFst),
          awaitPongFst > fst(joinPong) > assocLR,
        )
    }

    object Positive {
      def from[A](f: (Ping |*| A) -⚬ A): Deferrable.Positive[A] =
        new Deferrable.Positive[A] {
          override def awaitPingFst: (Ping |*| A) -⚬ A =
            f
        }

      given Deferrable.Positive[Ping] =
        from(joinPing)

      given Deferrable.Positive[Done] =
        Junction.Positive.junctionDone

      def byFst[A, B](using A: Deferrable.Positive[A]): Deferrable.Positive[A |*| B] =
        from(assocRL > fst(A.awaitPingFst))

      def bySnd[A, B](using B: Deferrable.Positive[B]): Deferrable.Positive[A |*| B] =
        from(XI > snd(B.awaitPingFst))
    }

    object Negative {
      def from[A](f: A -⚬ (Pong |*| A)): Deferrable.Negative[A] =
        new Deferrable.Negative[A] {
          override def awaitPongFst: A -⚬ (Pong |*| A) =
            f
        }

      given Deferrable.Negative[Pong] =
        from(joinPong)

      given Deferrable.Negative[Need] =
        Junction.Negative.junctionNeed

      def byFst[A, B](using A: Deferrable.Negative[A]): Deferrable.Negative[A |*| B] =
        from(fst(A.awaitPongFst) > assocLR)

      def bySnd[A, B](using B: Deferrable.Negative[B]): Deferrable.Negative[A |*| B] =
        from(snd(B.awaitPongFst) > XI)
    }

    def invert[A](d: Deferrable.Positive[A]): Deferrable.Negative[A] =
      new Deferrable.Negative[A] {
        override def awaitPongFst: A -⚬ (Pong |*| A) =
          introFst(lInvertPongPing) > assocLR > snd(d.awaitPingFst)
      }

    def invert[A](d: Deferrable.Negative[A]): Deferrable.Positive[A] =
      new Deferrable.Positive[A] {
        override def awaitPingFst: (Ping |*| A) -⚬ A =
          snd(d.awaitPongFst) > assocRL > elimFst(rInvertPingPong)
      }
  }

  object Junction {
    /** Represents ''a'' way how `A` can await (join) a positive (i.e. [[Done]]) signal. */
    trait Positive[A] extends Deferrable.Positive[A] {
      def awaitPosFst: (Done |*| A) -⚬ A

      override def awaitPingFst: (Ping |*| A) -⚬ A =
       fst(strengthenPing) > awaitPosFst

      def awaitPosSnd: (A |*| Done) -⚬ A =
        swap > awaitPosFst

      /** Alias for [[awaitPosFst]]. */
      def awaitPos: (Done |*| A) -⚬ A =
        awaitPosFst

      def detain: A -⚬ Detained[A] =
        Detained.untilDone(awaitPosFst)

      def law_awaitIdentity: Equal[(One |*| A) -⚬ A] =
        Equal(
          par(done, id) > awaitPosFst,
          elimFst,
        )

      def law_AwaitComposition: Equal[(Done |*| (Done |*| A)) -⚬ A] =
        Equal(
          par(id, awaitPosFst) > awaitPosFst,
          assocRL > par(join, id) > awaitPosFst,
        )
    }

    /** Represents ''a'' way how `A` can await (join) a negative (i.e. [[Need]]) signal. */
    trait Negative[A] extends Deferrable.Negative[A] {
      def awaitNegFst: A -⚬ (Need |*| A)

      override def awaitPongFst: A -⚬ (Pong |*| A) =
        awaitNegFst > fst(strengthenPong)

      def awaitNegSnd: A -⚬ (A |*| Need) =
        awaitNegFst > swap

      /** Alias for [[awaitNegFst]]. */
      def awaitNeg: A -⚬ (Need |*| A) =
        awaitNegFst

      def detain: A -⚬ Detained[A] =
        Detained.untilNeed(awaitNegFst)

      def law_awaitIdentity: Equal[A -⚬ (One |*| A)] =
        Equal(
          awaitNegFst > par(need, id),
          introFst,
        )

      def law_awaitComposition: Equal[A -⚬ (Need |*| (Need |*| A))] =
        Equal(
          awaitNegFst > par(id, awaitNegFst),
          awaitNegFst > par(joinNeed, id) > assocLR,
        )
    }

    object Positive {
      def apply[A](using A: Junction.Positive[A]): Junction.Positive[A] =
        A

      def from[A](await: (Done |*| A) -⚬ A): Junction.Positive[A] =
        new Junction.Positive[A] {
          override def awaitPosFst: (Done |*| A) -⚬ A =
            await
        }

      given junctionDone: Junction.Positive[Done] =
        from(join)

      def byFst[A, B](using A: Junction.Positive[A]): Junction.Positive[A |*| B] =
        from(assocRL > fst(A.awaitPosFst))

      def bySnd[A, B](using B: Junction.Positive[B]): Junction.Positive[A |*| B] =
        from(XI > par(id[A], B.awaitPosFst))

      def both[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |*| B] =
        from(par(fork, id) > IXI > par(A.awaitPosFst, B.awaitPosFst))

      def delegateToEither[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |+| B] =
        from( distributeL[Done, A, B] > |+|.bimap(A.awaitPosFst, B.awaitPosFst) )

      def delayEither[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |+| B] =
        from( delayEitherUntilDone > |+|.bimap(A.awaitPosFst, B.awaitPosFst) )

      def delegateToChosen[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |&| B] =
        from( coFactorL[Done, A, B] > |&|.bimap(A.awaitPosFst, B.awaitPosFst) )

      def delayChoice[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |&| B] =
        from( delayChoiceUntilDone > |&|.bimap(A.awaitPosFst, B.awaitPosFst) )

      def rec[F[_]](using F: Junction.Positive[F[Rec[F]]]): Junction.Positive[Rec[F]] =
        from(par(id, unpack) > F.awaitPosFst > pack)

      def rec[F[_]](using F: ∀[λ[x => Junction.Positive[F[x]]]]): Junction.Positive[Rec[F]] =
        rec(using F[Rec[F]])

      def rec[F[_]](f: Junction.Positive[Rec[F]] => Junction.Positive[F[Rec[F]]]): Junction.Positive[Rec[F]] =
        from(dsl.rec(g => par(id, unpack) > f(from(g)).awaitPosFst > pack))

      def insideInversion[A](using A: Junction.Positive[A]): Junction.Positive[-[A]] =
        Junction.Positive.from {
          λ { case d |*| na =>
            demandTogether(dii(d) |*| na)
              .contramap[A](λ { a =>
                val nd |*| d = constant(forevert[Done])
                nd |*| A.awaitPos(d |*| a)
              })
          }
        }
    }

    object Negative {
      def apply[A](using A: Junction.Negative[A]): Junction.Negative[A] =
        A

      def from[A](await: A -⚬ (Need |*| A)): Junction.Negative[A] =
        new Junction.Negative[A] {
          override def awaitNegFst: A -⚬ (Need |*| A) =
            await
        }

      given junctionNeed: Junction.Negative[Need] =
        from(joinNeed)

      def byFst[A, B](using A: Junction.Negative[A]): Junction.Negative[A |*| B] =
        from(par(A.awaitNegFst, id[B]) > assocLR)

      def bySnd[A, B](using B: Junction.Negative[B]): Junction.Negative[A |*| B] =
        from(par(id[A], B.awaitNegFst) > XI)

      def both[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |*| B] =
        from(par(A.awaitNegFst, B.awaitNegFst) > IXI > par(forkNeed, id))

      def delegateToEither[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        from( |+|.bimap(A.awaitNegFst, B.awaitNegFst) > factorL )

      def delayEither[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        from( |+|.bimap(A.awaitNegFst, B.awaitNegFst) > delayEitherUntilNeed )

      def delegateToChosen[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        from( |&|.bimap(A.awaitNegFst, B.awaitNegFst) > coDistributeL )

      def delayChoice[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        from( |&|.bimap(A.awaitNegFst, B.awaitNegFst) > delayChoiceUntilNeed )

      def rec[F[_]](using F: Junction.Negative[F[Rec[F]]]): Junction.Negative[Rec[F]] =
        from(unpack[F] > F.awaitNegFst > par(id, pack[F]))

      def rec[F[_]](using F: ∀[λ[x => Junction.Negative[F[x]]]]): Junction.Negative[Rec[F]] =
        rec(using F[Rec[F]])

      def rec[F[_]](f: Junction.Negative[Rec[F]] => Junction.Negative[F[Rec[F]]]): Junction.Negative[Rec[F]] =
        from(dsl.rec(g => unpack > f(from(g)).awaitNegFst > par(id, pack)))

      def insideInversion[A](using A: Junction.Negative[A]): Junction.Negative[-[A]] =
        Junction.Negative.from {
          λ { na =>
            na.contramap[-[Need] |*| A](λ { case nn |*| a =>
              val n |*| a1 = A.awaitNeg(a)
              returning(a, n supplyTo nn)
            }) :>> demandSeparately :>> fst(die)
          }
        }
    }

    /** [[Positive]] junction can be made to await a negative (i.e. [[Need]]) signal,
      * by inverting the signal ([[lInvertSignal]]) and awaiting the inverted positive signal.
      */
    def invert[A](A: Positive[A]): Negative[A] =
      new Negative[A] {
        override def awaitNegFst: A -⚬ (Need |*| A) =
          id                                 [                      A  ]
            ./>(introFst(lInvertSignal))  .to[ (Need |*|  Done) |*| A  ]
            ./>(assocLR)                  .to[  Need |*| (Done  |*| A) ]
            ./>.snd(A.awaitPosFst)        .to[  Need |*|            A  ]
      }

    /** [[Negative]] junction can be made to await a positive (i.e. [[Done]]) signal,
      * by inverting the signal ([[rInvertSignal]]) and awaiting the inverted negative signal.
      */
    def invert[A](A: Negative[A]): Positive[A] =
      new Positive[A] {
        override def awaitPosFst: (Done |*| A) -⚬ A =
          id                                 [  Done |*|            A  ]
            ./>.snd(A.awaitNegFst)        .to[  Done |*| (Need  |*| A) ]
            ./>(assocRL)                  .to[ (Done |*|  Need) |*| A  ]
            ./>(elimFst(rInvertSignal))   .to[                      A  ]
      }
  }

  object Signaling {
    /** Represents ''a'' way how `A` can produce a positive signal (i.e. [[Ping]] or [[Done]]). */
    trait Positive[A] {
      def notifyPosFst: A -⚬ (Ping |*| A)

      def notifyPosSnd: A -⚬ (A |*| Ping) =
        notifyPosFst > swap

      def signalPosFst: A -⚬ (Done |*| A) =
        notifyPosFst > par(strengthenPing, id)

      def signalPosSnd: A -⚬ (A |*| Done) =
        signalPosFst > swap

      /** Alias for [[signalPosFst]]. */
      def signalPos: A -⚬ (Done |*| A) =
        signalPosFst

      /** Alias for [[signalPosSnd]]. */
      def signalDone: A -⚬ (A |*| Done) =
        signalPosSnd

      def law_signalIdentity: Equal[A -⚬ (RTerminus |*| A)] =
        Equal(
          signalPosFst > par(delayIndefinitely, id),
          id[A] > introFst(done > delayIndefinitely),
        )

      def law_awaitComposition: Equal[A -⚬ (Done |*| (Done |*| A))] =
        Equal(
          signalPosFst > par(id, signalPosFst),
          signalPosFst > par(fork, id) > assocLR,
        )
    }

    /** Represents ''a'' way how `A` can produce a negative signal (i.e. [[Pong]] or [[Need]]). */
    trait Negative[A] {
      def notifyNegFst: (Pong |*| A) -⚬ A

      def notifyNegSnd: (A |*| Pong) -⚬ A =
        swap > notifyNegFst

      def signalNegFst: (Need |*| A) -⚬ A =
        par(strengthenPong, id) > notifyNegFst

      def signalNegSnd: (A |*| Need) -⚬ A =
        swap > signalNegFst

      /** Alias for [[signalNegFst]]. */
      def signalNeg: (Need |*| A) -⚬ A =
        signalNegFst

      def law_signalIdentity: Equal[(LTerminus |*| A) -⚬ A] =
        Equal(
          par(regressInfinitely, id) > signalNegFst,
          id[LTerminus |*| A] > elimFst(regressInfinitely > need),
        )

      def law_signalComposition: Equal[(Need |*| (Need |*| A)) -⚬ A] =
        Equal(
          par(id, signalNegFst) > signalNegFst,
          assocRL > par(forkNeed, id) > signalNegFst,
        )
    }

    object Positive {
      def from[A](notifyFst: A -⚬ (Ping |*| A)): Signaling.Positive[A] =
        new Signaling.Positive[A] {
          override def notifyPosFst: A -⚬ (Ping |*| A) =
            notifyFst
        }

      given signalingDone: Signaling.Positive[Done] =
        from(notifyDoneL)

      given Signaling.Positive[Ping] =
        from(forkPing)

      def byFst[A, B](using A: Signaling.Positive[A]): Signaling.Positive[A |*| B] =
        from(par(A.notifyPosFst, id[B]) > assocLR)

      def bySnd[A, B](using B: Signaling.Positive[B]): Signaling.Positive[A |*| B] =
        from(par(id[A], B.notifyPosFst) > XI)

      def both[A, B](using A: Signaling.Positive[A], B: Signaling.Positive[B]): Signaling.Positive[A |*| B] =
        from(par(A.notifyPosFst, B.notifyPosFst) > IXI > par(joinPing, id))

      /** Signals when it is decided which side of the [[|+|]] is present. */
      given either[A, B]: Signaling.Positive[A |+| B] =
        from(dsl.notifyEither[A, B])

      def either[A, B](A: Signaling.Positive[A], B: Signaling.Positive[B]): Signaling.Positive[A |+| B] =
        from(dsl.either(A.notifyPosFst > snd(injectL), B.notifyPosFst > snd(injectR)))

      def rec[F[_]](using F: Positive[F[Rec[F]]]): Positive[Rec[F]] =
        from(unpack > F.notifyPosFst > par(id, pack))

      def rec[F[_]](using F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        rec(using F[Rec[F]])

      def rec[F[_]](f: Positive[Rec[F]] => Positive[F[Rec[F]]]): Positive[Rec[F]] =
        from(dsl.rec(g => unpack > f(from(g)).notifyPosFst > par(id, pack)))
    }

    object Negative {
      def from[A](notifyFst: (Pong |*| A) -⚬ A): Signaling.Negative[A] =
        new Signaling.Negative[A] {
          override def notifyNegFst: (Pong |*| A) -⚬ A =
            notifyFst
        }

      given signalingNeed: Signaling.Negative[Need] =
        from(notifyNeedL)

      given Signaling.Negative[Pong] =
        from(forkPong)

      def byFst[A, B](using A: Signaling.Negative[A]): Signaling.Negative[A |*| B] =
        from(assocRL > fst(A.notifyNegFst))

      def bySnd[A, B](using B: Signaling.Negative[B]): Signaling.Negative[A |*| B] =
        from(XI > par(id[A], B.notifyNegFst))

      def both[A, B](using A: Signaling.Negative[A], B: Signaling.Negative[B]): Signaling.Negative[A |*| B] =
        from(par(joinPong, id) > IXI > par(A.notifyNegFst, B.notifyNegFst))

      /** Signals when the choice is made between [[A]] and [[B]]. */
      given choice[A, B]: Signaling.Negative[A |&| B] =
        from(dsl.notifyChoice[A, B])

      def choice[A, B](A: Signaling.Negative[A], B: Signaling.Negative[B]): Signaling.Negative[A |&| B] =
        from(dsl.choice(snd(chooseL) > A.notifyNegFst, snd(chooseR) > B.notifyNegFst))

      def rec[F[_]](using F: Negative[F[Rec[F]]]): Negative[Rec[F]] =
        from(par(id, unpack) > F.notifyNegFst > pack)

      def rec[F[_]](using F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        rec(using F[Rec[F]])

      def rec[F[_]](f: Negative[Rec[F]] => Negative[F[Rec[F]]]): Negative[Rec[F]] =
        from(dsl.rec(g => par(id, unpack) > f(from(g)).notifyNegFst > pack))
    }

    /** [[Signaling.Positive]] can be made to produce a negative (i.e. [[Need]]) signal,
      * by inverting the produced signal (via [[rInvertSignal]]).
      */
    def invert[A](A: Positive[A]): Negative[A] =
      new Negative[A] {
        override def notifyNegFst: (Pong |*| A) -⚬ A =
          id                                         [  Pong |*|            A  ]
            ./>.snd(A.notifyPosFst)               .to[  Pong |*| (Ping  |*| A) ]
            ./>(assocRL)                          .to[ (Pong |*|  Ping) |*| A  ]
            ./>(elimFst(swap > rInvertPingPong))  .to[                      A  ]
      }

    /** [[Signaling.Negative]] can be made to produce a positive (i.e. [[Done]]) signal,
      * by inverting the produced signal (via [[lInvertSignal]]).
      */
    def invert[A](A: Negative[A]): Positive[A] =
      new Positive[A] {
        override def notifyPosFst: A -⚬ (Ping |*| A) =
          id                                         [                      A  ]
            ./>(introFst(lInvertPongPing > swap)) .to[ (Ping |*|  Pong) |*| A  ]
            ./>(assocLR)                          .to[  Ping |*| (Pong  |*| A) ]
            ./>.snd(A.notifyNegFst)               .to[  Ping |*|            A  ]
      }
  }

  object SignalingJunction {
    /** Witnesses that [[A]] can both produce and await a positive (i.e. [[Done]]) signal. */
    trait Positive[A] extends Signaling.Positive[A] with Junction.Positive[A] {
      def delayUsing(f: Done -⚬ Done): A -⚬ A =
        signalPos > par(f, id) > awaitPos

      /** Expresses that awaiting one's own signal does not introduce a new causal dependency, i.e. that
        * the point of awaiting in [[A]] is causally dependent on the point of signaling in [[A]].
        */
      def law_positiveSignalThenAwaitIsId: Equal[A -⚬ A] =
        Equal[A -⚬ A](
          signalPos > awaitPos,
          id[A],
        )

      /** Expresses that awaiting a signal and then signaling does not speed up the original signal, i.e. that
        * the point of signaling in [[A]] is causally dependent on the point of awaiting in [[A]].
        */
      def law_positiveAwaitThenSignal: Equal[(Done |*| A) -⚬ (Done |*| A)] =
        Equal(
          awaitPos > signalPos,
          par(fork, id) > assocLR > par(id, awaitPos > signalPos) > assocRL > par(join, id),
        )
    }

    /** Witnesses that [[A]] can both produce and await a negative (i.e. [[Need]]) signal. */
    trait Negative[A] extends Signaling.Negative[A] with Junction.Negative[A] {
      def delayUsing(f: Need -⚬ Need): A -⚬ A =
        awaitNeg > par(f, id) > signalNeg

      /** Expresses that awaiting one's own signal does not introduce a new causal dependency, i.e. that
        * the point of awaiting in [[A]] is causally dependent on the point of signaling in [[A]].
        */
      def law_negativeAwaitThenSignalIsId: Equal[A -⚬ A] =
        Equal[A -⚬ A](
          awaitNeg > signalNeg,
          id[A],
        )

      /** Expresses that awaiting a signal and then signaling does not speed up the original signal, i.e. that
        * the point of signaling in [[A]] is causally dependent on the point of awaiting in [[A]].
        */
      def law_negativeSignalThenAwait: Equal[(Need |*| A) -⚬ (Need |*| A)] =
        Equal(
          signalNeg > awaitNeg,
          par(joinNeed, id) > assocLR > par(id, signalNeg > awaitNeg) > assocRL > par(forkNeed, id),
        )
    }

    object Positive {
      def from[A](s: Signaling.Positive[A], j: Junction.Positive[A]): SignalingJunction.Positive[A] =
        new SignalingJunction.Positive[A] {
          override def notifyPosFst: A -⚬ (Ping |*| A) = s.notifyPosFst
          override def awaitPosFst: (Done |*| A) -⚬ A = j.awaitPosFst
        }

      given signalingJunctionPositiveDone: SignalingJunction.Positive[Done] =
        Positive.from(
          Signaling.Positive.signalingDone,
          Junction.Positive.junctionDone,
        )

      def byFst[A, B](using A: Positive[A]): Positive[A |*| B] =
        Positive.from(
          Signaling.Positive.byFst[A, B],
          Junction.Positive.byFst[A, B],
        )

      def bySnd[A, B](using B: Positive[B]): Positive[A |*| B] =
        Positive.from(
          Signaling.Positive.bySnd[A, B],
          Junction.Positive.bySnd[A, B],
        )

      def both[A, B](using A: Positive[A], B: Positive[B]): Positive[A |*| B] =
        Positive.from(
          Signaling.Positive.both[A, B],
          Junction.Positive.both[A, B],
        )

      /** Signals when the `|+|` is decided, awaiting delays (the publication of) the decision and thed is delegated
        * to the respective side.
        */
      def eitherPos[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Positive[A |+| B] =
        Positive.from(
          Signaling.Positive.either[A, B],
          Junction.Positive.delayEither[A, B],
        )

      /** Signals when the `|+|` is decided, awaiting delays (the publication of) the decision and then is delegated
        * to the respective side, which awaits an inversion of the original signal.
        */
      def eitherNeg[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Positive[A |+| B] =
        Positive.from(
          Signaling.Positive.either[A, B],
          Junction.Positive.delayEither(using
            Junction.invert(A),
            Junction.invert(B),
          ),
        )

      def rec[F[_]](using F: Positive[F[Rec[F]]]): Positive[Rec[F]] =
        Positive.from(
          Signaling.Positive.rec(using F),
          Junction.Positive.rec(using F),
        )

      def rec[F[_]](using F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        rec(using F[Rec[F]])

      def rec[F[_]](
        f: Signaling.Positive[Rec[F]] => Signaling.Positive[F[Rec[F]]],
        g: Junction.Positive[Rec[F]] => Junction.Positive[F[Rec[F]]],
      ): SignalingJunction.Positive[Rec[F]] =
        from(Signaling.Positive.rec(f), Junction.Positive.rec(g))
    }

    object Negative {
      def from[A](s: Signaling.Negative[A], j: Junction.Negative[A]): SignalingJunction.Negative[A] =
        new SignalingJunction.Negative[A] {
          override def notifyNegFst: (Pong |*| A) -⚬ A = s.notifyNegFst
          override def awaitNegFst: A -⚬ (Need |*| A) = j.awaitNegFst
        }

      given SignalingJunction.Negative[Need] =
        Negative.from(
          Signaling.Negative.signalingNeed,
          Junction.Negative.junctionNeed,
        )

      def byFst[A, B](using A: Negative[A]): Negative[A |*| B] =
        Negative.from(
          Signaling.Negative.byFst[A, B],
          Junction.Negative.byFst[A, B],
        )

      def bySnd[A, B](using B: Negative[B]): Negative[A |*| B] =
        Negative.from(
          Signaling.Negative.bySnd[A, B],
          Junction.Negative.bySnd[A, B],
        )

      def both[A, B](using A: Negative[A], B: Negative[B]): Negative[A |*| B] =
        Negative.from(
          Signaling.Negative.both[A, B],
          Junction.Negative.both[A, B],
        )

      /** Signals when the choice (`|&|`) is made, awaiting delays the choice and then is delegated to the chosen side. */
      def choiceNeg[A, B](using A: Junction.Negative[A], B: Junction.Negative[B]): Negative[A |&| B] =
        Negative.from(
          Signaling.Negative.choice[A, B],
          Junction.Negative.delayChoice[A, B],
        )

      /** Signals when the choice (`|&|`) is made, awaiting delays the choice and then is delegated to the chosen side,
        * which awaits inversion of the original signal.
        */
      def choicePos[A, B](using A: Junction.Positive[A], B: Junction.Positive[B]): Negative[A |&| B] =
        Negative.from(
          Signaling.Negative.choice[A, B],
          Junction.Negative.delayChoice(using
            Junction.invert(A),
            Junction.invert(B),
          ),
        )

      def rec[F[_]](using F: Negative[F[Rec[F]]]): Negative[Rec[F]] =
        Negative.from(
          Signaling.Negative.rec(using F),
          Junction.Negative.rec(using F),
        )

      def rec[F[_]](using F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        rec(using F[Rec[F]])

      def rec[F[_]](
        f: Signaling.Negative[Rec[F]] => Signaling.Negative[F[Rec[F]]],
        g: Junction.Negative[Rec[F]] => Junction.Negative[F[Rec[F]]],
      ): SignalingJunction.Negative[Rec[F]] =
        from(Signaling.Negative.rec(f), Junction.Negative.rec(g))
    }
  }

  def notifyPosFst[A](using A: Signaling.Positive[A]): A -⚬ (Ping |*| A) =
    A.notifyPosFst

  def notifyPosSnd[A](using A: Signaling.Positive[A]): A -⚬ (A |*| Ping) =
    A.notifyPosSnd

  def notifyNegFst[A](using A: Signaling.Negative[A]): (Pong |*| A) -⚬ A =
    A.notifyNegFst

  def notifyNegSnd[A](using A: Signaling.Negative[A]): (A |*| Pong) -⚬ A =
    A.notifyNegSnd

  def signalPosFst[A](using A: Signaling.Positive[A]): A -⚬ (Done |*| A) =
    A.signalPosFst

  def signalPosSnd[A](using A: Signaling.Positive[A]): A -⚬ (A |*| Done) =
    A.signalPosSnd

  def signalDone[A](using A: Signaling.Positive[A]): A -⚬ (A |*| Done) =
    signalPosSnd

  def signalNegFst[A](using A: Signaling.Negative[A]): (Need |*| A) -⚬ A =
    A.signalNegFst

  def signalNegSnd[A](using A: Signaling.Negative[A]): (A |*| Need) -⚬ A =
    A.signalNegSnd

  def awaitPingFst[A](using A: Deferrable.Positive[A]): (Ping |*| A) -⚬ A =
    A.awaitPingFst

  def awaitPingSnd[A](using A: Deferrable.Positive[A]): (A |*| Ping) -⚬ A =
    A.awaitPingSnd

  def awaitPongFst[A](using A: Deferrable.Negative[A]): A -⚬ (Pong |*| A) =
    A.awaitPongFst

  def awaitPongSnd[A](using A: Deferrable.Negative[A]): A -⚬ (A |*| Pong) =
    A.awaitPongSnd

  def awaitPosFst[A](using A: Junction.Positive[A]): (Done |*| A) -⚬ A =
    A.awaitPosFst

  def awaitPosSnd[A](using A: Junction.Positive[A]): (A |*| Done) -⚬ A =
    A.awaitPosSnd

  def awaitNegFst[A](using A: Junction.Negative[A]): A -⚬ (Need |*| A) =
    A.awaitNegFst

  def awaitNegSnd[A](using A: Junction.Negative[A]): A -⚬ (A |*| Need) =
    A.awaitNegSnd

  def detain[A](using A: Junction.Positive[A]): A -⚬ Detained[A] =
    A.detain

  def defer[A](using A: Deferrable.Positive[A]): A -⚬ Deferred[A] =
    A.defer

  def delayUsing[A](f: Done -⚬ Done)(using A: SignalingJunction.Positive[A]): A -⚬ A =
    A.delayUsing(f)

  def delayUsing[A](f: Need -⚬ Need)(using A: SignalingJunction.Negative[A]): A -⚬ A =
    A.delayUsing(f)

  /** Obstructs interaction on the out-port (i.e. from the right) until [[Ping]] is received. */
  def blockOutportUntilPing[A]: (Ping |*| A) -⚬ A =
    injectLOnPing > either(id, id)

  /** Obstructs interaction on the in-port (i.e. from the left) until [[Pong]] is received. */
  def blockInportUntilPong[A]: A -⚬ (Pong |*| A) =
    choice(id, id) > chooseLOnPong

  /** Alias for [[sequence_PP]]. */
  def sequence[A: Signaling.Positive, B: Deferrable.Positive]: (A |*| B) -⚬ (A |*| B) =
    sequence_PP

  def sequence_PP[A, B](using A: Signaling.Positive[A], B: Deferrable.Positive[B]): (A |*| B) -⚬ (A |*| B) =
    fst(notifyPosSnd) > assocLR > snd(awaitPingFst)

  def sequence_PN[A, B](using A: Signaling.Positive[A], B: Deferrable.Negative[B]): (A |*| B) -⚬ (A |*| B) =
    fst(notifyPosSnd) > assocLR > snd(Deferrable.invert(B).awaitPingFst)

  def sequence_NP[A, B](using A: Signaling.Negative[A], B: Deferrable.Positive[B]): (A |*| B) -⚬ (A |*| B) =
    fst(Signaling.invert(A).notifyPosSnd) > assocLR > snd(awaitPingFst)

  def sequence_NN[A, B](using A: Signaling.Negative[A], B: Deferrable.Negative[B]): (A |*| B) -⚬ (A |*| B) =
    snd(awaitPongFst) > assocRL > fst(notifyNegSnd)

  extension [A](a: $[A])(using LambdaContext) {
    def sequence[B](b: $[B])(using A: Signaling.Positive[A], B: Deferrable.Positive[B]): $[A |*| B] =
      (a |*| b) > sequence_PP

    def sequence[B](f: Done -⚬ B)(using A: Signaling.Positive[A]): $[A |*| B] =
      a > signalPosSnd > snd(f)

    def sequenceAfter[B](b: $[B])(using A: Deferrable.Positive[A], B: Signaling.Positive[B]): $[A |*| B] =
      (b |*| a) > sequence_PP[B, A] > swap

    infix def waitFor(b: $[Done])(using A: Junction.Positive[A]): $[A] =
      (a |*| b) > awaitPosSnd

    infix def deferUntil(b: $[Ping])(using A: Deferrable.Positive[A]): $[A] =
      (a |*| b) > awaitPingSnd

    /** Obstructs further interaction until a [[Ping]] is received. */
    infix def blockUntil(b: $[Ping]): $[A] =
      blockOutportUntilPing(b |*| a)

    def raceAgainst[B](using SourcePos)(b: $[B])(using
      Signaling.Positive[A],
      Signaling.Positive[B],
    ): $[(A |*| B) |+| (A |*| B)] =
      lib.race[A, B](a |*| b)

    def raceAgainstInv[B](using SourcePos)(b: ??[B])(using
      Signaling.Positive[A],
      Signaling.Negative[B],
    ): ($[A |+| A], ??[B]) =
      (a :>> notifyPosFst) match {
        case ping |*| a =>
          (notifyNegFst >>: b) match {
            case pong |*| b =>
              ( switch ( racePair(ping |*| pong.asInput(lInvertPongPing)) )
                  .is { case InL(?(_)) => InL(a) }
                  .is { case InR(?(_)) => InR(a) }
                  .end
              , b
              )
      }
    }

    infix def raceAgainstInvWith[B, C](using SourcePos)(b: ??[B])(using
      Signaling.Positive[A],
      Signaling.Negative[B],
    )(f: LambdaContext ?=> Either[($[A], ??[B]), ($[A], ??[B])] => $[C]): $[C] = {
      val (aa, bb) = raceAgainstInv[B](b)
      switch ( aa )
        .is { case InL(a) => f(Left((a, bb))) }
        .is { case InR(a) => f(Right((a, bb))) }
        .end
    }
  }

  extension [A](a: ??[A]) {
    def raceAgainstStraight[B](using SourcePos, LambdaContext)(b: $[B])(using
      Signaling.Negative[A],
      Signaling.Positive[B],
    ): (??[A |&| A], $[B]) =
      (notifyNegFst >>: a) match {
        case pong |*| a =>
          (b :>> notifyPosFst) match {
            case ping |*| b =>
              ((selectPair >>: (pong |*| ping.asOutput(rInvertPingPong))) choose {
                case Left(one)  => (chooseL >>: a) alsoElim one
                case Right(one) => (chooseR >>: a) alsoElim one
              }, b)
          }
      }

    infix def raceWith[B, C](using SourcePos, LambdaContext)(b: $[B])(using
      Signaling.Negative[A],
      Signaling.Positive[B],
    )(f: LambdaContext ?=> Either[(??[A], $[B]), (??[A], $[B])] => ??[C]): ??[C] = {
      val (aa, bb) = raceAgainstStraight[B](b)
      aa choose {
        case Left(a)  => f(Left((a, bb)))
        case Right(a) => f(Right((a, bb)))
      }
    }

    def raceAgainst[B](using SourcePos, LambdaContext)(b: ??[B])(using
      Signaling.Negative[A],
      Signaling.Negative[B],
    ): ??[(A |*| B) |&| (A |*| B)] =
      lib.select[A, B] >>: (a |*| b)
  }

  def when[A](trigger: $[Done])(f: Done -⚬ A)(using LambdaContext): $[A] =
    trigger > f

  /** Races the two [[Done]] signals and
    *  - produces left if the first signal wins, in which case it returns the second signal that still
    *    has to be awaited;
    *  - produces right if the second signal wins, in which case it returns the first signal that still
    *    has to be awaited.
    * It is biased to the left: if both signals have arrived by the time of inquiry, returns left.
    */
  def raceDone: (Done |*| Done) -⚬ (Done |+| Done) =
    id                                     [           Done  |*|           Done  ]
      .>(par(notifyDoneL, notifyDoneL)) .to[ (Ping |*| Done) |*| (Ping |*| Done) ]
      .>(IXI)                           .to[ (Ping |*| Ping) |*| (Done |*| Done) ]
      .>(par(racePair, join))           .to[ ( One |+| One ) |*|      Done       ]
      .>(distributeR)                   .to[  (One |*| Done) |+| (One |*| Done)  ]
      .>(|+|.bimap(elimFst, elimFst))   .to[           Done  |+|          Done   ]

  /** Races two [[Need]] signals, i.e. signals traveling in the negative direction (i.e. opposite the `-⚬` arrow).
    * Based on which [[Need]] signal from the out-port wins the race,
    * selects one of the two [[Need]] signals from the in-port:
    *  - If the first signal from the out-port wins the race, selects the left signal from the in-port
    *    and pipes to it the remaining (i.e. the right) signal from the out-port.
    *  - If the second signal from the out-port wins the race, selects the right signal from the in-port
    *    and pipes to it the reamining (i.e. the left) signal from the out-port.
    * It is biased to the left: if both signals from the out-port have arrived by the time of inquiry,
    * selects the left signal from the in-port.
    */
  def selectNeed: (Need |&| Need) -⚬ (Need |*| Need) =
    id                                        [           Need  |*|           Need  ]
      ./<(par(notifyNeedL, notifyNeedL)) .from[ (Pong |*| Need) |*| (Pong |*| Need) ]
      ./<(IXI)                           .from[ (Pong |*| Pong) |*| (Need |*| Need) ]
      ./<(par(selectPair, joinNeed))     .from[ ( One |&| One ) |*|      Need       ]
      ./<(coDistributeR)                 .from[  (One |*| Need) |&| (One |*| Need)  ]
      ./<(|&|.bimap(introFst, introFst)) .from[           Need  |&|          Need   ]

  def raceBy[A, B](
    notifyA: A -⚬ (Ping |*| A),
    notifyB: B -⚬ (Ping |*| B),
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    id                                               [                  A  |*|           B         ]
      ./>(par(notifyA, notifyB))                  .to[        (Ping |*| A) |*| (Ping |*| B)        ]
      ./>(IXI)                                    .to[        (Ping |*| Ping) |*| (A |*| B)        ]
      ./>.fst(racePair)                           .to[        ( One |+| One ) |*| (A |*| B)        ]
      ./>(distributeR)                            .to[ (One |*| (A |*| B)) |+| (One |*| (A |*| B)) ]
      ./>(|+|.bimap(elimFst, elimFst))            .to[          (A |*| B)  |+|          (A |*| B)  ]

  def raceBy[A](
    notify: A -⚬ (Ping |*| A),
  ): (A |*| A) -⚬ ((A |*| A) |+| (A |*| A)) =
    raceBy(notify, notify)

  def race[A, B](using
    A: Signaling.Positive[A],
    B: Signaling.Positive[B],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    raceBy(A.notifyPosFst, B.notifyPosFst)

  def raceSwitch[A: Signaling.Positive, B: Signaling.Positive, C](
    caseFstWins: (A |*| B) -⚬ C,
    caseSndWins: (A |*| B) -⚬ C,
  ): (A |*| B) -⚬ C =
    race[A, B] > either(caseFstWins, caseSndWins)

  def raceWithL[X, A: Signaling.Positive, B: Signaling.Positive, C](
    caseFstWins: (X |*| (A |*| B)) -⚬ C,
    caseSndWins: (X |*| (A |*| B)) -⚬ C,
  ): (X |*| (A |*| B)) -⚬ C =
    par(id, race[A, B]) > distributeL > either(caseFstWins, caseSndWins)

  def raceWithR[A: Signaling.Positive, B: Signaling.Positive, Y, C](
    caseFstWins: ((A |*| B) |*| Y) -⚬ C,
    caseSndWins: ((A |*| B) |*| Y) -⚬ C,
  ): ((A |*| B) |*| Y) -⚬ C =
    par(race[A, B], id) > distributeR > either(caseFstWins, caseSndWins)

  def raceAgainstDoneL[A](using A: SignalingJunction.Positive[A]): (Done |*| A) -⚬ (A |+| A) =
    id                                               [  Done        |*|            A  ]
      ./>.snd(A.signalPos).>(assocRL)             .to[ (Done        |*|  Done) |*| A  ]
      ./>.fst(raceDone)                           .to[ (Done        |+|  Done) |*| A  ]
      ./>(distributeR)                            .to[ (Done |*| A) |+| (Done  |*| A) ]
      ./>(|+|.bimap(A.awaitPos, A.awaitPos))      .to[           A  |+|            A  ]

  def raceAgainstDoneR[A](using A: SignalingJunction.Positive[A]): (A |*| Done) -⚬ (A |+| A) =
    swap > raceAgainstDoneL > |+|.swap

  def selectBy[A, B](
    notifyA: ((Pong |*| A) -⚬ A),
    notifyB: ((Pong |*| B) -⚬ B),
  ): ((A |*| B) |&| (A |*| B)) -⚬ (A |*| B) =
    id                                               [          (A |*| B)  |&|          (A |*| B)  ]
      ./>(|&|.bimap(introFst, introFst))          .to[ (One |*| (A |*| B)) |&| (One |*| (A |*| B)) ]
      ./>(coDistributeR)                          .to[        ( One |&| One ) |*| (A |*| B)        ]
      ./>.fst(selectPair)                         .to[        (Pong |*| Pong) |*| (A |*| B)        ]
      ./>(IXI)                                    .to[        (Pong |*| A) |*| (Pong |*| B)        ]
      ./>(par(notifyA, notifyB))                  .to[                  A  |*|           B         ]

  def selectBy[A](
    notify: (Pong |*| A) -⚬ A,
  ): ((A |*| A) |&| (A |*| A)) -⚬ (A |*| A) =
    selectBy(notify, notify)

  def select[A, B](using
    A: Signaling.Negative[A],
    B: Signaling.Negative[B],
  ): ((A |*| B) |&| (A |*| B)) -⚬ (A |*| B) =
    selectBy(A.notifyNegFst, B.notifyNegFst)

  def selectWithL[Z, X, A: Signaling.Negative, B: Signaling.Negative](
    caseFstWins: Z -⚬ (X |*| (A |*| B)),
    caseSndWins: Z -⚬ (X |*| (A |*| B)),
  ): Z -⚬ (X |*| (A |*| B)) =
    choice(caseFstWins, caseSndWins) > coDistributeL > par(id, select[A, B])

  def selectWithR[Z, A: Signaling.Negative, B: Signaling.Negative, Y](
    caseFstWins: Z -⚬ ((A |*| B) |*| Y),
    caseSndWins: Z -⚬ ((A |*| B) |*| Y),
  ): Z -⚬ ((A |*| B) |*| Y) =
    choice(caseFstWins, caseSndWins) > coDistributeR > par(select[A, B], id)

  def select[Z, A: Signaling.Negative, B: Signaling.Negative](
    caseFstWins: Z -⚬ (A |*| B),
    caseSndWins: Z -⚬ (A |*| B),
  ): Z -⚬ (A |*| B) =
    choice(caseFstWins, caseSndWins) > select[A, B]

  def selectAgainstL[A](using A: SignalingJunction.Negative[A]): (A |&| A) -⚬ (Need |*| A) =
    id                                               [  Need        |*|            A  ]
      ./<.snd(A.signalNeg)./<(assocLR)          .from[ (Need        |*|  Need) |*| A  ]
      ./<.fst(selectNeed)                       .from[ (Need        |&|  Need) |*| A  ]
      ./<(coDistributeR)                        .from[ (Need |*| A) |&| (Need  |*| A) ]
      ./<(|&|.bimap(A.awaitNeg, A.awaitNeg))    .from[           A  |&|            A  ]

  def selectAgainstR[A](using A: SignalingJunction.Negative[A]): (A |&| A) -⚬ (A |*| Need) =
    |&|.swap > selectAgainstL > swap

  def racePreferred[A, B](using
    A: Signaling.Positive[A],
    B: Signaling.Positive[B],
  ): (Ping |*| (A |*| B)) -⚬ ((A |*| B) |+| (A |*| B)) =
    λ { case p |*| (a |*| b) =>
      switch ( race[Ping, A](p |*| a) )
        .is { case InL(?(_) |*| a) => InL(a |*| b) }
        .is { case InR(?(_) |*| a) => race[A, B](a |*| b) }
        .end
    }

  def raceHandicap[A, B, C](f: (Ping |*| B) -⚬ C)(using
    A: Signaling.Positive[A],
    C: Signaling.Positive[C],
  ): (A |*| (Ping |*| B)) -⚬ ((A |*| B) |+| ((A |*| C) |+| (A |*| C))) =
    λ { case a |*| (p |*| b) =>
      switch ( race[A, Ping](a |*| p) )
        .is { case InL(a |*| ?(_)) => InL(a |*| b) }
        .is { case InR(a |*| p)    => InR(race[A, C](a |*| f(p |*| b))) }
        .end
    }

  trait Getter[S, A] { self =>
    def getL[B](that: Getter[A, B])(using B: Cosemigroup[B]): S -⚬ (B |*| S)

    def extendJunction(using Junction.Positive[A]): Junction.Positive[S]

    def getL(using A: Cosemigroup[A]): S -⚬ (A |*| S) =
      getL(Getter.identity[A])

    def getR(using A: Cosemigroup[A]): S -⚬ (S |*| A) =
      getL > swap

    def awaitFst(using Junction.Positive[A]): (Done |*| S) -⚬ S =
      extendJunction.awaitPosFst

    def awaitSnd(using Junction.Positive[A]): (S |*| Done) -⚬ S =
      swap > awaitFst

    infix def andThen[B](that: Getter[A, B]): Getter[S, B] =
      new Getter[S, B] {
        override def getL[C](next: Getter[B, C])(using C: Cosemigroup[C]): S -⚬ (C |*| S) =
          self.getL(that andThen next)

        override def extendJunction(using Junction.Positive[B]): Junction.Positive[S] =
          self.extendJunction(using that.extendJunction)
      }

    infix def compose[T](that: Getter[T, S]): Getter[T, A] =
      that andThen this

    def |+|[T](that: Getter[T, A]): Getter[S |+| T, A] =
      new Getter[S |+| T, A] {
        override def getL[B](next: Getter[A, B])(using B: Cosemigroup[B]): (S |+| T) -⚬ (B |*| (S |+| T)) =
          lib.|+|.bimap(self.getL(next), that.getL(next)) > factorL

        override def extendJunction(using Junction.Positive[A]): Junction.Positive[S |+| T] =
          new Junction.Positive[S |+| T] {
            override def awaitPosFst: (Done |*| (S |+| T)) -⚬ (S |+| T) =
              distributeL > lib.|+|.bimap(self.awaitFst, that.awaitFst)
          }
      }
  }

  object Getter {
    def identity[A]: Getter[A, A] =
      new Getter[A, A] {
        override def getL[B](that: Getter[A, B])(using B: Cosemigroup[B]): A -⚬ (B |*| A) =
          that.getL

        override def getL(using A: Cosemigroup[A]): A -⚬ (A |*| A) =
          A.split

        override def andThen[B](that: Getter[A, B]): Getter[A, B] =
          that

        override def extendJunction(using A: Junction.Positive[A]): Junction.Positive[A] =
          A
      }
  }

  trait Lens[S, A] extends Getter[S, A] {
    def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| S) -⚬ (Y |*| S)

    def read[Y](f: A -⚬ (Y |*| A)): S -⚬ (Y |*| S) =
      introFst[S] > modify[One, Y](elimFst > f)

    def write[X](f: (X |*| A) -⚬ A): (X |*| S) -⚬ S =
      modify[X, One](f > introFst) > elimFst

    override def getL[B](that: Getter[A, B])(using B: Cosemigroup[B]): S -⚬ (B |*| S) =
      read(that.getL)

    override def extendJunction(using A: Junction.Positive[A]): Junction.Positive[S] =
      new Junction.Positive[S] {
        def awaitPosFst: (Done |*| S) -⚬ S = write(A.awaitPosFst)
      }

    infix def andThen[B](that: Lens[A, B]): Lens[S, B] =
      new Lens[S, B] {
        def modify[X, Y](f: (X |*| B) -⚬ (Y |*| B)): (X |*| S) -⚬ (Y |*| S) =
          Lens.this.modify(that.modify(f))
      }

    def compose[T](that: Lens[T, S]): Lens[T, A] =
      that andThen this

    def |+|[T](that: Lens[T, A]): Lens[S |+| T, A] =
      new Lens[S |+| T, A] {
        def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| (S |+| T)) -⚬ (Y |*| (S |+| T)) =
          distributeL[X, S, T] > lib.|+|.bimap(Lens.this.modify(f), that.modify(f)) > factorL
      }
  }

  object Lens {
    def rec[F[_]]: Lens[Rec[F], F[Rec[F]]] =
      new Lens[Rec[F], F[Rec[F]]] {
        def modify[X, Y](f: (X |*| F[Rec[F]]) -⚬ (Y |*| F[Rec[F]])): (X |*| Rec[F]) -⚬ (Y |*| Rec[F]) =
          id[X |*| Rec[F]]
            ./>.snd(unpack)
            ./>(f)
            ./>.snd(pack)
      }
  }

  trait Transportive[F[_]] extends Functor[F] {
    def inL[A, B]: (A |*| F[B]) -⚬ F[A |*| B]
    def outL[A, B]: F[A |*| B] -⚬ (A |*| F[B])

    def inR[A, B]: (F[A] |*| B) -⚬ F[A |*| B] =
      swap[F[A], B] > inL > lift(swap[B, A])

    def outR[A, B]: F[A |*| B] -⚬ (F[A] |*| B) =
      lift(swap[A, B]) > outL > swap[B, F[A]]

    /** Alias for [[outL]]. */
    def excludeFst[A, B]: F[A |*| B] -⚬ (A |*| F[B]) =
      outL

    /** Alias for [[outR]]. */
    def excludeSnd[A, B]: F[A |*| B] -⚬ (F[A] |*| B) =
      outR

    /** Alias for [[inL]]. */
    def includeFst[A, B]: (A |*| F[B]) -⚬ F[A |*| B] =
      inL

    /** Alias for [[inR]]. */
    def includeSnd[A, B]: (F[A] |*| B) -⚬ F[A |*| B] =
      inR

    def getL[A](using A: Cosemigroup[A]): F[A] -⚬ (A |*| F[A]) =
      lift(A.split) > outL

    def getR[A](using A: Cosemigroup[A]): F[A] -⚬ (F[A] |*| A) =
      getL[A] > swap

    def lens[A]: Lens[F[A], A] = new Lens[F[A], A] {
      def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| F[A]) -⚬ (Y |*| F[A]) =
        inL > lift(f) > outL
    }
  }

  object Transportive {
    def apply[F[_]](using F: Transportive[F]): Transportive[F] =
      F

    /** Pair is covariant in the first argument. */
    def fst[B]: Transportive[λ[x => x |*| B]] =
      new Transportive[λ[x => x |*| B]] {
        override val category: Category[-⚬] = dsl.category
        def lift[A1, A2](f: A1 -⚬ A2): (A1 |*| B) -⚬ (A2 |*| B) = par(f, id)
        def inL[A1, A2]: (A1 |*| (A2 |*| B)) -⚬ ((A1 |*| A2) |*| B) = assocRL
        def outL[A1, A2]: ((A1 |*| A2) |*| B) -⚬ (A1 |*| (A2 |*| B)) = assocLR
      }

    /** Pair is covariant in the second argument. */
    def snd[A]: Transportive[λ[x => A |*| x]] =
      new Transportive[λ[x => A |*| x]] {
        override val category: Category[-⚬] = dsl.category
        def lift[B1, B2](f: B1 -⚬ B2): (A |*| B1) -⚬ (A |*| B2) = par(id, f)
        def inL[B1, B2]: (B1 |*| (A |*| B2)) -⚬ (A |*| (B1 |*| B2)) =
          assocRL[B1, A, B2] > dsl.fst(swap) > assocLR
        def outL[B1, B2]: (A |*| (B1 |*| B2)) -⚬ (B1 |*| (A |*| B2)) =
          assocRL[A, B1, B2] > dsl.fst(swap) > assocLR
      }
  }

  type Id[A] = A

  given Transportive[Id] with {
    override val category: Category[-⚬] = dsl.category
    def lift[A, B](f: A -⚬ B): Id[A] -⚬ Id[B] = f
    def inL[A, B]: (A |*| Id[B]) -⚬ Id[A |*| B] = id
    def outL[A, B]: Id[A |*| B] -⚬ (A |*| Id[B]) = id
  }

  object |+| {
    def assocLR[A, B, C]: ((A |+| B) |+| C) -⚬ (A |+| (B |+| C)) =
      either(either(injectL, andThen(injectL, injectR)), andThen(injectR, injectR))

    def assocRL[A, B, C]: (A |+| (B |+| C)) -⚬ ((A |+| B) |+| C) =
      either(andThen(injectL, injectL), either(andThen(injectR, injectL), injectR))

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |+| C )-⚬ (B |+| D) =
      either(f > injectL, g > injectR)

    def lmap[A, B, A1](f: A -⚬ A1): (A |+| B) -⚬ (A1 |+| B) =
      either(f > injectL, injectR)

    def rmap[A, B, B1](f: B -⚬ B1): (A |+| B) -⚬ (A |+| B1) =
      either(injectL, f > injectR)

    def swap[A, B]: (A |+| B) -⚬ (B |+| A) =
      either(injectR, injectL)

    def IXI[A, B, C, D]: ((A |+| B) |+| (C |+| D)) -⚬ ((A |+| C) |+| (B |+| D)) =
      either(
        either(injectL ∘ injectL, injectR ∘ injectL),
        either(injectL ∘ injectR, injectR ∘ injectR),
      )

    def switchWithL[A, B, L, C](
      caseLeft:  (L |*| A) -⚬ C,
      caseRight: (L |*| B) -⚬ C,
    ): (L |*| (A |+| B)) -⚬ C =
      distributeL > either(caseLeft, caseRight)

    def switchWithR[A, B, R, C](
      caseLeft:  (A |*| R) -⚬ C,
      caseRight: (B |*| R) -⚬ C,
    ): ((A |+| B) |*| R) -⚬ C =
      distributeR > either(caseLeft, caseRight)

    /** Alias for [[notifyEither]]:
      * Adds a [[Ping]] that fires when it is decided whether `A |+| B` actually contains the left side or the right side.
      */
    def notify[A, B]: (A |+| B) -⚬ (Ping |*| (A |+| B)) =
      notifyEither

    /** Adds a [[Done]] that completes when it is decided whether `A |+| B` actually contains the left side or the right side. */
    def signal[A, B]: (A |+| B) -⚬ (Done |*| (A |+| B)) =
      notify > fst(strengthenPing)

    /** Adds a [[Ping]] to the left case that fires when the [[|+|]] is decided. */
    def notifyL[A, B]: (A |+| B) -⚬ ((Ping |*| A) |+| B) =
      notify > distributeL > rmap(elimFst(dismissPing))

    /** Adds a [[Ping]] to the right case that fires when the [[|+|]] is decided. */
    def notifyR[A, B]: (A |+| B) -⚬ (A |+| (Ping |*| B)) =
      notify > distributeL > lmap(elimFst(dismissPing))

    /** Adds a [[Done]] to the left case that completes when the [[|+|]] is decided. */
    def signalL[A, B]: (A |+| B) -⚬ ((Done |*| A) |+| B) =
      notify > distributeL > bimap(fst(strengthenPing), elimFst(dismissPing))

    /** Adds a [[Done]] to the right case that completes when the [[|+|]] is decided. */
    def signalR[A, B]: (A |+| B) -⚬ (A |+| (Done |*| B)) =
      notify > distributeL > bimap(elimFst(dismissPing), fst(strengthenPing))

    val bifunctor: Bifunctor[|+|] =
      new Bifunctor[|+|] {
        override val category =
          dsl.category

        override def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |+| C )-⚬ (B |+| D) =
          bimap(f, g)
      }

    /** Disjoint union is covariant in the left argument. */
    def left[B]: Functor[[x] =>> x |+| B] =
      bifunctor.fst[B]

    /** Disjoint union is covariant in the right argument. */
    def right[A]: Monad[[x] =>> A |+| x] =
      new Monad[[x] =>> A |+| x] {
        override val category: Category[-⚬] =
          dsl.category

        override def pure[B]: B -⚬ (A |+| B) =
          injectR

        override def lift[B, C](f: B -⚬ C): (A |+| B) -⚬ (A |+| C) =
          rmap(f)

        override def flatten[B]: (A |+| (A |+| B)) -⚬ (A |+| B) =
          either(injectL, id)
      }
  }

  object |&| {
    def assocLR[A, B, C]: ((A |&| B) |&| C) -⚬ (A |&| (B |&| C)) =
      choice(andThen(chooseL, chooseL), choice(andThen(chooseL, chooseR), chooseR))

    def assocRL[A, B, C]: (A |&| (B |&| C)) -⚬ ((A |&| B) |&| C) =
      choice(choice(chooseL, andThen(chooseR, chooseL)), andThen(chooseR, chooseR))

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |&| C) -⚬ (B |&| D) =
      choice(chooseL > f, chooseR > g)

    def lmap[A, B, A1](f: A -⚬ A1): (A |&| B) -⚬ (A1 |&| B) =
      choice(chooseL > f, chooseR)

    def rmap[A, B, B1](f: B -⚬ B1): (A |&| B) -⚬ (A |&| B1) =
      choice(chooseL, chooseR > f)

    def swap[A, B]: (A |&| B) -⚬ (B |&| A) =
      choice(chooseR, chooseL)

    def IXI[A, B, C, D]: ((A |&| B) |&| (C |&| D)) -⚬ ((A |&| C) |&| (B |&| D)) =
      choice(
        choice(chooseL > chooseL, chooseR > chooseL),
        choice(chooseL > chooseR, chooseR > chooseR),
      )

    /** Alias for [[notifyChoice]]:
      * Adds a [[Pong]] that fires when it is known which side of the choice (`A |&| B`) has been chosen.
      */
    def notify[A, B]: (Pong |*| (A |&| B)) -⚬ (A |&| B) =
      notifyChoice

    /** Adds a [[Need]] that completes when it is known which side of the choice (`A |&| B`) has been chosen. */
    def signal[A, B]: (Need |*| (A |&| B)) -⚬ (A |&| B) =
      fst(strengthenPong) > notify

    /** Adds a [[Pong]] to the left case that fires when the choice is made. */
    def notifyL[A, B]: ((Pong |*| A) |&| B) -⚬ (A |&| B) =
      rmap(introFst(dismissPong)) > coDistributeL > notify

    /** Adds a [[Pong]] to the right case that fires when the choice is made. */
    def notifyR[A, B]: (A |&| (Pong |*| B)) -⚬ (A |&| B) =
      lmap(introFst(dismissPong)) > coDistributeL > notify

    /** Adds a [[Need]] to the left case that completes when the choice is made. */
    def signalL[A, B]: ((Need |*| A) |&| B) -⚬ (A |&| B) =
      bimap(fst(strengthenPong), introFst(dismissPong)) > coDistributeL > notify

    /** Adds a [[Need]] to the right case that completes when the choice is made. */
    def signalR[A, B]: (A |&| (Need |*| B)) -⚬ (A |&| B) =
      bimap(introFst(dismissPong), fst(strengthenPong)) > coDistributeL > notify

    val bifunctor: Bifunctor[|&|] =
      new Bifunctor[|&|] {
        override val category =
          dsl.category

        override def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |&| C) -⚬ (B |&| D) =
          bimap(f, g)
      }

    /** Choice is covariant in the left argument. */
    def left[B]: Functor[λ[x => x |&| B]] =
      bifunctor.fst[B]

    /** Choice is covariant in the right argument. */
    def right[A]: Functor[λ[x => A |&| x]] =
      bifunctor.snd[A]
  }

  given fstFunctor[B]: Transportive[[x] =>> x |*| B] = Transportive.fst[B]
  given sndFunctor[A]: Transportive[[x] =>> A |*| x] = Transportive.snd[A]

  given Bifunctor[|+|] = |+|.bifunctor

  given Bifunctor[|&|] = |&|.bifunctor

  implicit class LinearFunctionOps[A, B](self: A -⚬ B) {
    /** No-op used for documentation purposes: explicitly states the input type of this linear function. */
    def from[Z](using ev: A =:= Z): Z -⚬ B = ev.substituteCo[λ[x => x -⚬ B]](self)

    /** No-op used for documentation purposes: explicitly states the output type of this linear function. */
    def to[C](using ev: B =:= C): A -⚬ C = ev.substituteCo(self)

    /** No-op used for documentation purposes: explicitly states the full type of this linear function. */
    def as[C](using ev: (A -⚬ B) =:= C): C = ev(self)

    def ∘[Z](g: Z -⚬ A): Z -⚬ B = dsl.andThen(g, self)

    /** Focuses on function's output. */
    def /> : FocusedCo[[x] =>> A -⚬ x, B] =
      new FocusedCo[[x] =>> A -⚬ x, B](self)

    /** Focuses on function's input. */
    def /< : FocusedContra[[x] =>> x -⚬ B, A] =
      new FocusedContra[[x] =>> x -⚬ B, A](self)
  }

  /** Focused on `B` in `F[B]`, where `B` is in a covariant position. */
  class FocusedCo[F[_], B](f: F[B])(using F: Externalizer[F]) {
    def map[C](g: B -⚬ C): F[C] = F.lift(g)(f)

    /** Alias for [[map]]. */
    def apply[C](g: B -⚬ C): F[C] = map(g)

    def subst[C](using ev: B =:= C): F[C] =
      ev.substituteCo(f)

    def unsubst[C](using ev: C =:= B): F[C] =
      ev.substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(using ev: B =:= G[C]): FocusedCo[λ[x => F[G[x]]], C] =
      new FocusedCo[λ[x => F[G[x]]], C](ev.substituteCo(f))(using F ∘ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(using ev: B =:= G[C]): FocusedContra[λ[x => F[G[x]]], C] =
      new FocusedContra[λ[x => F[G[x]]], C](ev.substituteCo(f))(using F ∘ G)

    def co[G[_]](using G: Functor[G], U: Unapply[B, G]): FocusedCo[λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(using U.ev)

    def contra[G[_]](using G: ContraFunctor[G], U: Unapply[B, G]): FocusedContra[λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(using U.ev)

    def bi[G[_, _]](using G: Bifunctor[G], U: Unapply2[B, G]): FocusedBi[λ[(x, y) => F[G[x, y]]], U.A, U.B] =
      new FocusedBi[λ[(x, y) => F[G[x, y]]], U.A, U.B](U.ev.substituteCo(f))(F ∘ G)
  }

  class FocusedBi[F[_, _], B1, B2](f: F[B1, B2])(F: BiExternalizer[F]) {
    def map[C1, C2](g: B1 -⚬ C1, h: B2 -⚬ C2): F[C1, C2] =
      F.lift(g, h)(f)

    def fst: FocusedCo[F[*, B2], B1] =
      new FocusedCo[F[*, B2], B1](f)(using F.fst)

    def snd: FocusedCo[F[B1, *], B2] =
      new FocusedCo[F[B1, *], B2](f)(using F.snd)
  }

  implicit class FocusedOnPairCo[F[_], B1, B2](f: FocusedCo[F, B1 |*| B2]) {
    def fst: FocusedCo[[x] =>> F[x |*| B2], B1] =
      f.zoomCo(Functor[[x] =>> x |*| B2])

    def snd: FocusedCo[[x] =>> F[B1 |*| x], B2] =
      f.zoomCo(Functor[[x] =>> B1 |*| x])
  }

  implicit class FocusedOnPlusCo[F[_], B1, B2](f: FocusedCo[F, B1 |+| B2]) {
    def left: FocusedCo[λ[x => F[x |+| B2]], B1] =
      f.zoomCo(|+|.left[B2])

    def right: FocusedCo[λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(|+|.right[B1])
  }

  implicit class FocusedOnChoiceCo[F[_], B1, B2](f: FocusedCo[F, B1 |&| B2]) {
    def choiceL: FocusedCo[λ[x => F[x |&| B2]], B1] =
      f.zoomCo(|&|.left[B2])

    def choiceR: FocusedCo[λ[x => F[B1 |&| x]], B2] =
      f.zoomCo(|&|.right[B1])
  }

  /** Focused on `B` in `F[B]`, where `B` is in a contravariant position. */
  class FocusedContra[F[_], B](f: F[B])(using F: ContraExternalizer[F]) {
    def contramap[A](g: A -⚬ B): F[A] =
      F.lift(g)(f)

    /** Alias for [[contramap]]. */
    def apply[A](g: A -⚬ B): F[A] =
      contramap(g)

    def subst[C](using ev: B =:= C): F[C] =
      ev.substituteCo(f)

    def unsubst[C](using ev: C =:= B): F[C] =
      ev.substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(using ev: B =:= G[C]): FocusedContra[λ[x => F[G[x]]], C] =
      new FocusedContra[λ[x => F[G[x]]], C](ev.substituteCo(f))(using F ∘ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(using ev: B =:= G[C]): FocusedCo[λ[x => F[G[x]]], C] =
      new FocusedCo[λ[x => F[G[x]]], C](ev.substituteCo(f))(using F ∘ G)

    def co[G[_]](using G: Functor[G], U: Unapply[B, G]): FocusedContra[λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(using U.ev)

    def contra[G[_]](using G: ContraFunctor[G], U: Unapply[B, G]): FocusedCo[λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(using U.ev)
  }

  implicit class FocusedOnPairContra[A, F[_], B1, B2](f: FocusedContra[F, B1 |*| B2]) {
    def fst: FocusedContra[[x] =>> F[x |*| B2], B1] =
      f.zoomCo(Functor[[x] =>> x |*| B2])

    def snd: FocusedContra[[x] =>> F[B1 |*| x], B2] =
      f.zoomCo(Functor[[x] =>> B1 |*| x])
  }

  /** Extends the focus to the left/right side of the (currently focused) producer choice. */
  implicit class FocusedOnPlusContra[A, F[_], B1, B2](f: FocusedContra[F, B1 |+| B2]) {
    def left: FocusedContra[λ[x => F[x |+| B2]], B1] =
      f.zoomCo(|+|.left[B2])

    def right: FocusedContra[λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(|+|.right[B1])
  }

  /** Extends the focus to the left/right side of the (currently focused) consumer choice. */
  implicit class FocusedOnChoiceContra[A, F[_], B1, B2](f: FocusedContra[F, B1 |&| B2]) {
    def choiceL: FocusedContra[λ[x => F[x |&| B2]], B1] =
      f.zoomCo(|&|.left[B2])

    def choiceR: FocusedContra[λ[x => F[B1 |&| x]], B2] =
      f.zoomCo(|&|.right[B1])
  }

  def IXI[A, B, C, D]: ((A|*|B)|*|(C|*|D)) -⚬
  //                     |    \   /    |
  //                     |     \ /     |
  //                     |      X      |
  //                     |     / \     |
  //                     |    /   \    |
                       ((A|*|C)|*|(B|*|D)) =
    id                             [ (A |*| B) |*| (C |*| D) ]
      ./>(assocLR)              .to[ A |*| (B |*| (C |*| D)) ]
      ./>.snd(assocRL)          .to[ A |*| ((B |*| C) |*| D) ]
      ./>.snd.fst(swap)         .to[ A |*| ((C |*| B) |*| D) ]
      ./>.snd(assocLR)          .to[ A |*| (C |*| (B |*| D)) ]
      ./>(assocRL)              .to[ (A |*| C) |*| (B |*| D) ]

  def IX[A, B, C]: ((A|*|B)|*| C) -⚬
    //               |    \   /
    //               |     \ /
    //               |      X
    //               |     / \
    //               |    /   \
                   ((A|*|C)|*| B) =
    assocLR[A, B, C] > par(id, swap) > assocRL

  def XI[A, B, C]: (A |*|(B|*|C)) -⚬
    //               \   /    |
    //                \ /     |
    //                 X      |
    //                / \     |
    //               /   \    |
                   (B |*|(A|*|C)) =
    assocRL[A, B, C] > par(swap, id) > assocLR

  def IV[A, B, C, D](f: (B |*| C) -⚬ D): ( ( A |*| B ) |*| C ) -⚬
    //                                       |      \     /
    //                                       |       \   /
    //                                       |        \ /
                                           ( A   |*|   D ) =
    assocLR > snd(f)

  def VI[A, B, C, D](f: (A |*| B) -⚬ D): ( A |*| ( B |*| C ) ) -⚬
    //                                      \     /      |
    //                                       \   /       |
    //                                        \ /        |
                                             ( D   |*|   C ) =
    assocRL > fst(f)

  /** Λ is the uppercase Greek letter lambda. */
  def IΛ[A, B, C, D](f: B -⚬ (C |*| D)): ( A   |*|   B ) -⚬
    //                                     |        / \
    //                                     |       /   \
    //                                     |      /     \
                                       ( ( A |*| C ) |*| D ) =
    snd(f) > assocRL

  /** Λ is the uppercase Greek letter lambda. */
  def ΛI[A, B, C, D](f: A -⚬ (B |*| C)): ( A   |*|   D ) -⚬
    //                                    / \        |
    //                                   /   \       |
    //                                  /     \      |
                                     ( B |*| ( C |*| D ) ) =
    fst(f) > assocLR

  /** From the choice ''available'' on the right (`C |&| D`), choose the one corresponding to the choice ''made''
    * on the left (`A |+| B`): if on the left there is `A`, choose `C`, if on the left thre is `B`, choose `D`.
    */
  def matchingChoiceLR[A, B, C, D]: ((A |+| B) |*| (C |&| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |+| B) |*| (C |&| D)]
      ./>(distributeR)          .to[(A |*| (C |&| D)) |+| (B |*| (C |&| D))]
      ./>.left.snd(chooseL)     .to[(A |*|  C       ) |+| (B |*| (C |&| D))]
      ./>.right.snd(chooseR)    .to[(A |*|  C       ) |+| (B |*|        D )]

  /** From the choice ''available'' on the left (`A |&| B`), choose the one corresponding to the choice ''made''
    * on the right (`C |+| D`): if on the right there is `C`, choose `A`, if on the right there is `D`, choose `B`.
    */
  def matchingChoiceRL[A, B, C, D]: ((A |&| B) |*| (C |+| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |&| B) |*| (C |+| D)]
      ./>(distributeL)          .to[((A |&| B) |*| C) |+| ((A |&| B) |*| D)]
      ./>.left.fst(chooseL)     .to[( A        |*| C) |+| ((A |&| B) |*| D)]
      ./>.right.fst(chooseR)    .to[( A        |*| C) |+| (       B  |*| D)]

  /** Present a choice between two pairs (`(A |*| B) |&| (C |*| D)`) as a choice (`A |&| C`) between the first
    * parts of the respective pairs and on the side provide the other part of the chosen input pair, i.e. either
    * `B` or `D` (`B |+| D`).
    */
  def subordinateSnd[A, B, C, D]: ((A |*| B) |&| (C |*| D)) -⚬ ((A |&| C) |*| (B |+| D)) =
    id                                 [ (A |*|  B       ) |&| (C |*|        D ) ]
      ./>.choiceL.snd(injectL)      .to[ (A |*| (B |+| D)) |&| (C |*|        D ) ]
      ./>.choiceR.snd(injectR)      .to[ (A |*| (B |+| D)) |&| (C |*| (B |+| D)) ]
      ./>(coDistributeR)

  /** Present a choice between two pairs (`(A |*| B) |&| (C |*| D)`) as a choice (`B |&| D`) between the second
    * parts of the respective pairs and on the side provide the other part of the chosen input pair, i.e. either
    * `A` or `C` (`A |+| C`).
    */
  def subordinateFst[A, B, C, D]: ((A |*| B) |&| (C |*| D)) -⚬ ((A |+| C) |*| (B |&| D)) =
    id                                 [ ( A        |*|  B) |&| (       C  |*| D) ]
      ./>.choiceL.fst(injectL)      .to[ ((A |+| C) |*|  B) |&| (       C  |*| D) ]
      ./>.choiceR.fst(injectR)      .to[ ((A |+| C) |*|  B) |&| ((A |+| C) |*| D) ]
      ./>(coDistributeL)            .to[  (A |+| C) |*| (B  |&|                D) ]

  /** Notifies when the [[|+|]] is decided _and_ the present side notifies using the respective given function. */
  def notifyEitherAndSides[A, B](
    notifyL: A -⚬ (Ping |*| A),
    notifyR: B -⚬ (Ping |*| B),
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    id                                           [                      A  |+|           B   ]
      ./>(|+|.bimap(notifyL, notifyR))        .to[            (Ping |*| A) |+| (Ping |*| B)  ]
      ./>(notifyEither)                       .to[  Ping |*| ((Ping |*| A) |+| (Ping |*| B)) ]
      ./>.snd(factorL)                        .to[  Ping |*| (Ping  |*| (A |+|           B)) ]
      ./>(assocRL)                            .to[ (Ping |*|  Ping) |*| (A |+|           B)  ]
      ./>.fst(joinPing)                       .to[      Ping        |*| (A |+|           B)  ]

  /** Notifies when the [[|+|]] is decided _and_ the present side notifies. */
  def notifyEitherAndSides[A, B](using
    A: Signaling.Positive[A],
    B: Signaling.Positive[B],
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    notifyEitherAndSides(A.notifyPosFst, B.notifyPosFst)

  /** Notifies when the [[|+|]] is decided _and_ if it is left, the left side notifies using the given function. */
  def notifyEitherAndLeft[A, B](
    notifyL: A -⚬ (Ping |*| A),
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    notifyEitherAndSides(notifyL, introFst(ping))

  /** Notifies when the [[|+|]] is decided _and_ if it is left, the left side notifies. */
  def notifyEitherAndLeft[A, B](using
    A: Signaling.Positive[A],
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    notifyEitherAndLeft(A.notifyPosFst)

  /** Notifies when the [[|+|]] is decided _and_ if it is right, the right side notifies using the given function. */
  def notifyEitherAndRight[A, B](
    notifyR: B -⚬ (Ping |*| B),
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    notifyEitherAndSides(introFst(ping), notifyR)

  /** Notifies when the [[|+|]] is decided _and_ if it is right, the right side notifies. */
  def notifyEitherAndRight[A, B](using
    B: Signaling.Positive[B],
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
   notifyEitherAndRight(B.notifyPosFst)

  /** Notifies when the choice ([[|&|]]) is made _and_ the chosen side notifies using the respective given function. */
  def notifyChoiceAndSides[A, B](
    notifyL: (Pong |*| A) -⚬ A,
    notifyR: (Pong |*| B) -⚬ B,
  ): (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    id                                        [                      A  |&|           B   ]
      ./<(|&|.bimap(notifyL, notifyR))   .from[            (Pong |*| A) |&| (Pong |*| B)  ]
      ./<(notifyChoice)                  .from[  Pong |*| ((Pong |*| A) |&| (Pong |*| B)) ]
      ./<.snd(coFactorL)                 .from[  Pong |*| (Pong  |*| (A |&|           B)) ]
      ./<(assocLR)                       .from[ (Pong |*|  Pong) |*| (A |&|           B)  ]
      ./<.fst(joinPong)                  .from[      Pong        |*| (A |&|           B)  ]

  /** Notifies when the choice ([[|&|]]) is made _and_ the chosen side notifies. */
  def notifyChoiceAndSides[A, B](using
    A: Signaling.Negative[A],
    B: Signaling.Negative[B],
  ): (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    notifyChoiceAndSides(A.notifyNegFst, B.notifyNegFst)

  /** Notifies when the choice ([[|&|]]) is made _and_ if it is left, the left side notifies using the given function. */
  def notifyChoiceAndLeft[A, B](
    notifyL: (Pong |*| A) -⚬ A,
  ): (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    notifyChoiceAndSides(notifyL, elimFst(pong))

  /** Notifies when the choice ([[|&|]]) is made _and_ if it is left, the left side notifies. */
  def notifyChoiceAndLeft[A, B](using
    A: Signaling.Negative[A],
  ): (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    notifyChoiceAndLeft(A.notifyNegFst)

  /** Notifies when the choice ([[|&|]]) is made _and_ if it is right, the right side notifies using the given function. */
  def notifyChoiceAndRight[A, B](
    notifyR: (Pong |*| B) -⚬ B,
  ): (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    notifyChoiceAndSides(elimFst(pong), notifyR)

  /** Notifies when the choice ([[|&|]]) is made _and_ if it is right, the right side notifies. */
  def notifyChoiceAndRight[A, B](using
    B: Signaling.Negative[B],
  ): (Pong |*| (A |&| B)) -⚬ (A |&| B) =
    notifyChoiceAndRight(B.notifyNegFst)

  def injectLWhenDone[A, B]: (Done |*| A) -⚬ ((Done |*| A) |+| B) =
    par(notifyDoneL, id) > assocLR > injectLOnPing

  def injectRWhenDone[A, B]: (Done |*| B) -⚬ (A |+| (Done |*| B)) =
    par(notifyDoneL, id) > assocLR > injectROnPing

  def chooseLWhenNeed[A, B]: ((Need |*| A) |&| B) -⚬ (Need |*| A) =
    chooseLOnPong > assocRL > par(notifyNeedL, id)

  def chooseRWhenNeed[A, B]: (A |&| (Need |*| B)) -⚬ (Need |*| B) =
    chooseROnPong > assocRL > par(notifyNeedL, id)

  def injectLOnPong[A, B]: A -⚬ (Pong |*| (A |+| B)) =
    id[A] > introFst(lInvertPongPing) > assocLR > snd(injectLOnPing)

  def injectROnPong[A, B]: B -⚬ (Pong |*| (A |+| B)) =
    id[B] > introFst(lInvertPongPing) > assocLR > snd(injectROnPing)

  def chooseLOnPing[A, B]: (Ping |*| (A |&| B)) -⚬ A =
    snd(chooseLOnPong) > assocRL > elimFst(rInvertPingPong)

  def chooseROnPing[A, B]: (Ping |*| (A |&| B)) -⚬ B =
    snd(chooseROnPong) > assocRL > elimFst(rInvertPingPong)

  def chooseLWhenDone[A, B]: (Done |*| (A |&| B)) -⚬ (Done |*| A) =
    id                                                      [ Done |*| (                    A   |&| B) ]
      ./>.snd.choiceL(introFst(lInvertSignal) > assocLR) .to[ Done |*| ((Need |*| (Done |*| A)) |&| B) ]
      ./>.snd(chooseLWhenNeed)                           .to[ Done |*|  (Need |*| (Done |*| A))        ]
      ./>(assocRL).>(elimFst(rInvertSignal))             .to[                      Done |*| A          ]

  def chooseRWhenDone[A, B]: (Done |*| (A |&| B)) -⚬ (Done |*| B) =
    id                                                      [ Done |*| (A |&|                     B  ) ]
      ./>.snd.choiceR(introFst(lInvertSignal) > assocLR) .to[ Done |*| (A |&| (Need |*| (Done |*| B))) ]
      ./>.snd(chooseRWhenNeed)                           .to[ Done |*|        (Need |*| (Done |*| B))  ]
      ./>(assocRL > elimFst(rInvertSignal))              .to[                            Done |*| B    ]

  def injectLWhenNeed[A, B]: (Need |*| A) -⚬ (Need |*| (A |+| B)) =
    id                                                      [                      Need |*| A   ]
      ./>(introFst(lInvertSignal)).>(assocLR)            .to[ Need |*|  (Done |*| (Need |*| A)) ]
      ./>.snd(injectLWhenDone)                           .to[ Need |*| ((Done |*| (Need |*| A)) |+| B) ]
      ./>.snd.left(assocRL > elimFst(rInvertSignal))     .to[ Need |*| (                    A   |+| B) ]

  def injectRWhenNeed[A, B]: (Need |*| B) -⚬ (Need |*| (A |+| B)) =
    id                                                      [                            Need |*| B    ]
      ./>(introFst(lInvertSignal)).>(assocLR)            .to[ Need |*|        (Done |*| (Need |*| B))  ]
      ./>.snd(injectRWhenDone)                           .to[ Need |*| (A |+| (Done |*| (Need |*| B))) ]
      ./>.snd.right(assocRL > elimFst(rInvertSignal))    .to[ Need |*| (A |+|                     B  ) ]

  def delayEitherUntilPing[A, B]: (Ping |*| (A |+| B)) -⚬ (A |+| B) =
    distributeL > either(injectLOnPing, injectROnPing)

  def delayChoiceUntilPong[A, B]: (A |&| B) -⚬ (Pong |*| (A |&| B)) =
    choice(chooseLOnPong, chooseROnPong) > coDistributeL

  def delayEitherUntilPong[A, B]: (A |+| B) -⚬ (Pong |*| (A |+| B)) =
    either(injectLOnPong, injectROnPong)

  def delayChoiceUntilPing[A, B]: (Ping |*| (A |&| B)) -⚬ (A |&| B) =
    choice(chooseLOnPing, chooseROnPing)

  def delayEitherUntilDone[A, B]: (Done |*| (A |+| B)) -⚬ ((Done |*| A) |+| (Done |*| B)) =
    id                                                               [  Done |*| (A  |+|           B) ]
      .>(distributeL)                                             .to[ (Done |*|  A) |+| (Done |*| B) ]
      .>(either(injectLWhenDone, injectRWhenDone))                .to[ (Done |*|  A) |+| (Done |*| B) ]

  def delayEitherAndSidesUntilDone[A, B](using
    A: Junction.Positive[A],
    B: Junction.Positive[B],
  ): (Done |*| (A |+| B)) -⚬ (A |+| B) =
    delayEitherUntilDone[A, B] > |+|.bimap(A.awaitPosFst, B.awaitPosFst)

  def delayChoiceUntilNeed[A, B]: ((Need |*| A) |&| (Need |*| B)) -⚬ (Need |*| (A |&| B)) =
    id                                                               [ (Need |*|  A) |&| (Need |*| B) ]
      .>(choice(chooseLWhenNeed, chooseRWhenNeed))                .to[ (Need |*|  A) |&| (Need |*| B) ]
      .>(coDistributeL)                                           .to[  Need |*| (A  |&|           B) ]

  def delayChoiceAndSidesUntilNeed[A, B](using
    A: Junction.Negative[A],
    B: Junction.Negative[B],
  ): (A |&| B) -⚬ (Need |*| (A |&| B)) =
    |&|.bimap(A.awaitNegFst, B.awaitNegFst) > delayChoiceUntilNeed[A, B]

  def delayEitherUntilNeed[A, B]: ((Need |*| A) |+| (Need |*| B)) -⚬ (Need |*| (A |+| B)) =
    id                                                               [ (Need |*|  A) |+| (Need |*| B) ]
      .>(either(injectLWhenNeed, injectRWhenNeed))                .to[  Need |*| (A  |+|           B) ]

  def delayEitherAndSidesUntilNeed[A, B](using
    A: Junction.Negative[A],
    B: Junction.Negative[B],
  ): (A |+| B) -⚬ (Need |*| (A |+| B)) =
    |+|.bimap(A.awaitNegFst, B.awaitNegFst) > delayEitherUntilNeed[A, B]

  def delayChoiceUntilDone[A, B]: (Done |*| (A |&| B)) -⚬ ((Done |*| A) |&| (Done |*| B)) =
    id                                                               [  Done |*| (A  |&|           B) ]
      .>(choice(chooseLWhenDone[A, B], chooseRWhenDone[A, B]))    .to[ (Done |*|  A) |&| (Done |*| B) ]

  def delayChoiceAndSidesUntilDone[A, B](using
    A: Junction.Positive[A],
    B: Junction.Positive[B],
  ): (Done |*| (A |&| B)) -⚬ (A |&| B) =
    delayChoiceUntilDone[A, B] > |&|.bimap(A.awaitPosFst, B.awaitPosFst)

  /** Injects `A` from the the second in-port to the left side of the `|+|` in the out-port, but only after
    * the `Done` signal from the first in-port arrives. That means that the consumer of `A |+| B` will see it
    * as undecided until the `Done` signal arrives. This is different from `awaitPosFst[A] > injectL[A, B]`,
    * in which the consumer of `A |+| B` knows immediately that it is the left case.
    *
    * This is a convenience method on top of [[injectLWhenDone]] that which absorbs the `Done` signal using
    * the given [[Junction.Positive]].
    */
  def awaitInjectL[A, B](using A: Junction.Positive[A]): (Done |*| A) -⚬ (A |+| B) =
    injectLWhenDone./>.left(A.awaitPos)

  /** Analogous to [[joinInjectL]], but injects to the right. */
  def awaitInjectR[A, B](using B: Junction.Positive[B]): (Done |*| B) -⚬ (A |+| B) =
    injectRWhenDone./>.right(B.awaitPos)

  /** Chooses the left alternative `A` of the choice `A |&| B`, but only after the `Need` signal from the first
    * out-port arrives. Until then, the producer of `A |&| B` will see it as undecided. This is different from
    * `chooseL[A, B] > awaitNegFst[A]`, in which the producer of `A |&| B` knows immediately that the left side
    * is chosen.
    */
  def awaitChooseL[A, B](using A: Junction.Negative[A]): (A |&| B) -⚬ (Need |*| A) =
    id[A |&| B]./>.choiceL(A.awaitNeg) > chooseLWhenNeed

  /** Analogous to [[awaitChooseL]], but chooses the right side. */
  def awaitChooseR[A, B](using B: Junction.Negative[B]): (A |&| B) -⚬ (Need |*| B) =
    id[A |&| B]./>.choiceR(B.awaitNeg) > chooseRWhenNeed

  /** Analogous to [[awaitChooseL]], but awaits a positive (i.e. [[Done]]) signal. */
  def awaitPosChooseL[A, B](using A: Junction.Positive[A]): (Done |*| (A |&| B)) -⚬ A =
    par(id, awaitChooseL(using Junction.invert(A))) > assocRL > elimFst(rInvertSignal)

  /** Analogous to [[awaitChooseR]], but awaits a positive (i.e. [[Done]]) signal. */
  def awaitPosChooseR[A, B](using B: Junction.Positive[B]): (Done |*| (A |&| B)) -⚬ B =
    par(id, awaitChooseR(using Junction.invert(B))) > assocRL > elimFst(rInvertSignal)

  /** Creates a pair of mutually recursive functions. */
  def rec2[A, B, C, D](
    f: (A -⚬ B, C -⚬ D) => A -⚬ B,
    g: (A -⚬ B, C -⚬ D) => C -⚬ D,
  ): (A -⚬ B, C -⚬ D) =
    (
      rec { (ab: A -⚬ B) => f(ab, rec { (cd: C -⚬ D) => g(ab, cd) }) },
      rec { (cd: C -⚬ D) => g(rec { (ab: A -⚬ B) => f(ab, cd) }, cd) },
    )

  def rec2[A, B, C, D](
    fs: (A -⚬ B, C -⚬ D) => (A -⚬ B, C -⚬ D),
  ): (A -⚬ B, C -⚬ D) =
    rec2(
      (f, g) => fs(f, g)._1,
      (f, g) => fs(f, g)._2,
    )

  def rec3[A, B, C, D, E, F](
    f: (A -⚬ B, C -⚬ D, E -⚬ F) => A -⚬ B,
    g: (A -⚬ B, C -⚬ D, E -⚬ F) => C -⚬ D,
    h: (A -⚬ B, C -⚬ D, E -⚬ F) => E -⚬ F,
  ): (A -⚬ B, C -⚬ D, E -⚬ F) =
    (
      rec { (ab: A -⚬ B) =>
        f(
          ab,
          rec { (cd: C -⚬ D) => g(ab, cd, rec { (ef: E -⚬ F) => h(ab, cd, ef) }) },
          rec { (ef: E -⚬ F) => h(ab, rec { (cd: C -⚬ D) => g(ab, cd, ef) }, ef) },
        )
      },
      rec { (cd: C -⚬ D) =>
        g(
          rec { (ab: A -⚬ B) => f(ab, cd, rec { (ef: E -⚬ F) => h(ab, cd, ef) }) },
          cd,
          rec { (ef: E -⚬ F) => h(rec { (ab: A -⚬ B) => f(ab, cd, ef) }, cd, ef) },
        )
      },
      rec { (ef: E -⚬ F) =>
        h(
          rec { (ab: A -⚬ B) => f(ab, rec { (cd: C -⚬ D) => g(ab, cd, ef) }, ef) },
          rec { (cd: C -⚬ D) => g(rec { (ab: A -⚬ B) => f(ab, cd, ef) }, cd, ef) },
          ef,
        )
      },
    )

  def rec3[A, B, C, D, E, F](
    fs: (A -⚬ B, C -⚬ D, E -⚬ F) => (A -⚬ B, C -⚬ D, E -⚬ F),
  ): (A -⚬ B, C -⚬ D, E -⚬ F) =
    rec3(
      (f, g, h) => fs(f, g, h)._1,
      (f, g, h) => fs(f, g, h)._2,
      (f, g, h) => fs(f, g, h)._3,
    )

  opaque type Bool = Done |+| Done
  object Bool {
    val constTrue: Done -⚬ Bool =
      injectL

    val constFalse: Done -⚬ Bool =
      injectR

    def switch[R](
      caseTrue : Done -⚬ R,
      caseFalse: Done -⚬ R,
    ): Bool -⚬ R =
      either(caseTrue, caseFalse)

    def switchWithL[A, R](
      caseTrue : (A |*| Done) -⚬ R,
      caseFalse: (A |*| Done) -⚬ R,
    ): (A |*| Bool) -⚬ R =
      distributeL > either(caseTrue, caseFalse)

    def switchWithR[A, R](
      caseTrue : (Done |*| A) -⚬ R,
      caseFalse: (Done |*| A) -⚬ R,
    ): (Bool |*| A) -⚬ R =
      distributeR > either(caseTrue, caseFalse)

    def ifThenElse[A, B, C](ifTrue: (Done |*| A) -⚬ B, ifFalse: (Done |*| A) -⚬ C): (Bool |*| A) -⚬ (B |+| C) =
      id                                   [          Bool |*| A           ]
        .>(distributeR)                 .to[ (Done |*| A) |+| (Done |*| A) ]
        .>(|+|.bimap(ifTrue, ifFalse))  .to[        B     |+|        C     ]
  }

  def testBy[A, B, K: Cosemigroup: Junction.Positive](
    aKey: Getter[A, K],
    bKey: Getter[B, K],
    pred: (K |*| K) -⚬ Bool,
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) = {
    import Bool.*

    val awaitL: (Done |*| (A |*| B)) -⚬ (A |*| B) =
      (aKey compose Transportive.fst[B].lens[A]).awaitFst

    id[A |*| B]
      ./>(par(aKey.getL, bKey.getL))
      ./>(IXI)
      ./>.fst(pred)
      ./>(ifThenElse(awaitL, awaitL))
  }

  object Compared {
    opaque type Compared[A, B] = (A |*| B) |+| ((A |*| B) |+| (A |*| B))

    // constructors
    def lt   [A, B]: (A |*| B) -⚬ Compared[A, B] = injectL
    def equiv[A, B]: (A |*| B) -⚬ Compared[A, B] = injectL > injectR
    def gt   [A, B]: (A |*| B) -⚬ Compared[A, B] = injectR > injectR

    /** Destructor. */
    def compared[A, B, C](
      caseLt: (A |*| B) -⚬ C,
      caseEq: (A |*| B) -⚬ C,
      caseGt: (A |*| B) -⚬ C,
    ): Compared[A, B] -⚬ C =
      either(caseLt, either(caseEq, caseGt))

    /** Destructor that allows to combine the compared values with another value. */
    def elimWith[A, B, C, D](
      caseLt: ((A |*| B) |*| C) -⚬ D,
      caseEq: ((A |*| B) |*| C) -⚬ D,
      caseGt: ((A |*| B) |*| C) -⚬ D,
    ): (Compared[A, B] |*| C) -⚬ D =
      id[ Compared[A, B] |*| C ]                    .to[ ((A |*| B)        |+| ( (A |*| B)        |+|  (A |*| B))) |*| C   ]
        ./>(distributeR)./>.right(distributeR)      .to[ ((A |*| B) |*| C) |+| (((A |*| B) |*| C) |+| ((A |*| B)   |*| C)) ]
        ./>(either(caseLt, either(caseEq, caseGt))) .to[                    D                                              ]

    def enrichWith[A, B, C, S, T](
      f: ((A |*| B) |*| C) -⚬ (S |*| T),
    )
    : (Compared[A, B] |*| C) -⚬ Compared[S, T] =
      id[ Compared[A, B] |*| C ]                .to[ ((A |*| B)        |+| ( (A |*| B)        |+|  (A |*| B))) |*| C   ]
        ./>(distributeR)./>.right(distributeR)  .to[ ((A |*| B) |*| C) |+| (((A |*| B) |*| C) |+| ((A |*| B)   |*| C)) ]
        ./>(|+|.bimap(f, |+|.bimap(f, f)))      .to[     (S |*| T)     |+| (    (S |*| T)     |+|      (S |*| T)     ) ]

    def bifunctorCompared: Bifunctor[Compared] =
      new Bifunctor[Compared] {
        override val category =
          dsl.category

        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): Compared[A, C] -⚬ Compared[B, D] = {
          Bifunctor[|+|].lift(
            par(f, g),
            Bifunctor[|+|].lift(
              par(f, g),
              par(f, g),
            )
          )
        }
      }
  }

  import Compared.*

  def compareBy[A, B, K1 : CloseableCosemigroup : Junction.Positive, K2 : CloseableCosemigroup : Junction.Positive](
    aKey: Getter[A, K1],
    bKey: Getter[B, K2],
  )(using
    cmp: Comparable[K1, K2],
  ): (A |*| B) -⚬ Compared[A, B] = {
    cmp.contramap(aKey, bKey).compare
  }

  trait Comparable[A, B] { self =>
    def compare: (A |*| B) -⚬ Compared[A, B]

    def contramap[S, T](
      f: Getter[S, A],
      g: Getter[T, B],
    )(using
      A: CloseableCosemigroup[A],
      B: CloseableCosemigroup[B],
      AJ: Junction.Positive[A],
      BJ: Junction.Positive[B],
    ): Comparable[S, T] =
      new Comparable[S, T] {
        private val absorb: ((A |*| B) |*| (S |*| T)) -⚬ (S |*| T) =
          id                                    [ (A    |*| B) |*| (S    |*| T) ]
            ./>(IXI)                         .to[ (A    |*| S) |*| (B    |*| T) ]
            ./>.fst.fst(A.close)             .to[ (Done |*| S) |*| (B    |*| T) ]
            ./>.snd.fst(B.close)             .to[ (Done |*| S) |*| (Done |*| T) ]
            ./>(par(f.awaitFst, g.awaitFst)) .to[           S  |*|           T  ]

        override def compare: (S |*| T) -⚬ Compared[S, T] = {
          id[ S |*| T ]
            ./>(par(f.getL, g.getL))
            ./>(IXI)
            ./>.fst(self.compare)
            ./>(Compared.enrichWith(absorb))
        }
      }
  }

  def dualSymmetric[A, B](ev: Dual[A, B]): Dual[B, A] = new Dual[B, A] {
    val lInvert: One -⚬ (A |*| B) = andThen(ev.lInvert, swap)
    val rInvert: (B |*| A) -⚬ One = andThen(swap, ev.rInvert)
  }

  given Dual[One, One] with {
    val lInvert: One -⚬ (One |*| One) = introSnd
    val rInvert: (One |*| One) -⚬ One = elimSnd
  }

  def rInvertPair[A, B, Ȧ, Ḃ](
    rInvertA: (A |*| Ȧ) -⚬ One,
    rInvertB: (B |*| Ḃ) -⚬ One,
  ): ((A |*| B) |*| (Ȧ |*| Ḃ)) -⚬ One =
    id[(A |*| B) |*| (Ȧ |*| Ḃ)]               .to[ (A |*| B) |*| (Ȧ |*| Ḃ) ]
      .>(IXI)                                 .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
      .>(parToOne(rInvertA, rInvertB))        .to[           One           ]

  def lInvertPair[A, B, Ȧ, Ḃ](
    lInvertA: One -⚬ (Ȧ |*| A),
    lInvertB: One -⚬ (Ḃ |*| B),
  ): One -⚬ ((Ȧ |*| Ḃ) |*| (A |*| B)) =
    id[One]                                   .to[           One           ]
      .>(parFromOne(id, id))                  .to[    One    |*|    One    ]
      .>(par(lInvertA, lInvertB))             .to[ (Ȧ |*| A) |*| (Ḃ |*| B) ]
      .>(IXI)                                 .to[ (Ȧ |*| Ḃ) |*| (A |*| B) ]

  given pairDuality[A, B, Ȧ, Ḃ](using a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |*| B, Ȧ |*| Ḃ] with {
    val lInvert: One -⚬ ((Ȧ |*| Ḃ) |*| (A |*| B)) =
      lInvertPair(a.lInvert, b.lInvert)

    val rInvert: ((A |*| B) |*| (Ȧ |*| Ḃ)) -⚬ One =
      rInvertPair(a.rInvert, b.rInvert)
  }

  def rInvertEither[A, B, Ȧ, Ḃ](
    rInvertA: (A |*| Ȧ) -⚬ One,
    rInvertB: (B |*| Ḃ) -⚬ One,
  ): ((A |+| B) |*| (Ȧ |&| Ḃ)) -⚬ One =
    id                                 [ (A |+| B) |*| (Ȧ |&| Ḃ) ]
      .>(matchingChoiceLR)          .to[ (A |*| Ȧ) |+| (B |*| Ḃ) ]
      .>(either(rInvertA, rInvertB)).to[           One           ]

  def lInvertChoice[A, B, Ȧ, Ḃ](
    lInvertA: One -⚬ (Ȧ |*| A),
    lInvertB: One -⚬ (Ḃ |*| B),
  ): One -⚬ ((Ȧ |&| Ḃ) |*| (A |+| B)) =
    id                                 [           One           ]
      .>(choice(lInvertA, lInvertB)).to[ (Ȧ |*| A) |&| (Ḃ |*| B) ]
      .>(subordinateSnd)            .to[ (Ȧ |&| Ḃ) |*| (A |+| B) ]

  given eitherChoiceDuality[A, B, Ȧ, Ḃ](using a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |+| B, Ȧ |&| Ḃ] with {
    val rInvert: ((A |+| B) |*| (Ȧ |&| Ḃ)) -⚬ One =
      rInvertEither(a.rInvert, b.rInvert)

    val lInvert: One -⚬ ((Ȧ |&| Ḃ) |*| (A |+| B)) =
      lInvertChoice(a.lInvert, b.lInvert)
  }

  given choiceEitherDuality[A, B, Ȧ, Ḃ](using a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |&| B, Ȧ |+| Ḃ] =
    dualSymmetric(eitherChoiceDuality(using dualSymmetric(a), dualSymmetric(b)))

  given doneNeedDuality: Dual[Done, Need] with {
    val rInvert: (Done |*| Need) -⚬ One = rInvertSignal
    val lInvert: One -⚬ (Need |*| Done) = lInvertSignal
  }

  /** Evidence that if `A` is dual to `B`, then `F[A]` is dual to `G[B]`. */
  trait Dual1[F[_], G[_]] {
    def rInvert[A, Ā](rInvert: (A |*| Ā) -⚬ One): (F[A] |*| G[Ā]) -⚬ One
    def lInvert[A, Ā](lInvert: One -⚬ (Ā |*| A)): One -⚬ (G[Ā] |*| F[A])

    val rInvertVal: [x, y] => ((x |*| y) -⚬ One) => ((F[x] |*| G[y]) -⚬ One) =
      [A, B] => (rInvert: (A |*| B) -⚬ One) => Dual1.this.rInvert(rInvert)

    val lInvertVal: [x, y] => (One -⚬ (y |*| x)) => (One -⚬ (G[y] |*| F[x])) =
      [A, B] => (lInvert: One -⚬ (B |*| A)) => Dual1.this.lInvert(lInvert)

    def rInvertFlippedTAgs: [Ā, A] => (rInvert: (A |*| Ā) -⚬ One) => ((F[A] |*| G[Ā]) -⚬ One) =
      [Ā, A] => (rInvert: (A |*| Ā) -⚬ One) => Dual1.this.rInvert[A, Ā](rInvert)

    def lInvertFlippedTArgs: [Ā, A] => (lInvert: One -⚬ (Ā |*| A)) => (One -⚬ (G[Ā] |*| F[A])) =
      [Ā, A] => (lInvert: One -⚬ (Ā |*| A)) => Dual1.this.lInvert[A, Ā](lInvert)

    def apply[A, Ā](ev: Dual[A, Ā]): Dual[F[A], G[Ā]] =
      new Dual[F[A], G[Ā]] {
        val rInvert: (F[A] |*| G[Ā]) -⚬ One = Dual1.this.rInvert(ev.rInvert)
        val lInvert: One -⚬ (G[Ā] |*| F[A]) = Dual1.this.lInvert(ev.lInvert)
      }
  }

  def rInvertRec[F[_], G[_]](
    rInvertSub: [x, y] => ((x |*| y) -⚬ One) => ((F[x] |*| G[y]) -⚬ One),
  ): (Rec[F] |*| Rec[G]) -⚬ One =
    rec { self =>
      par(unpack, unpack) > rInvertSub(self)
    }

  def lInvertRec[F[_], G[_]](
    lInvertSub: [x, y] => (One -⚬ (x |*| y)) => (One -⚬ (F[x] |*| G[y])),
  ): One -⚬ (Rec[F] |*| Rec[G]) =
    rec { self =>
      lInvertSub(self) > par(pack, pack)
    }

  /** If `F[A]` is dual to `G[B]` for all dual pairs `A`, `B`, then `Rec[F]` is dual to `Rec[G]`. */
  def dualRec[F[_], G[_]](ev: Dual1[F, G]): Dual[Rec[F], Rec[G]] =
    new Dual[Rec[F], Rec[G]] {
      val rInvert: (Rec[F] |*| Rec[G]) -⚬ One =
        rInvertRec(ev.rInvertVal)

      val lInvert: One -⚬ (Rec[G] |*| Rec[F]) =
        lInvertRec(ev.lInvertFlippedTArgs)
    }

  opaque type Maybe[A] = One |+| A
  object Maybe {
    def empty[A]: One -⚬ Maybe[A] =
      injectL

    def just[A]: A -⚬ Maybe[A] =
      injectR

    def toEither[A]: Maybe[A] -⚬ (One |+| A) =
      id

    def map[A, B](f: A -⚬ B): Maybe[A] -⚬ Maybe[B] =
      |+|.rmap(f)

    def getOrElse[A](f: One -⚬ A): Maybe[A] -⚬ A =
      either(f, id)

    def discard[A](f: A -⚬ One): Maybe[A] -⚬ One =
      either(id, f)

    def discard[A](using A: Comonoid[A]): Maybe[A] -⚬ One =
      discard(A.counit)

    def neglect[A](f: A -⚬ Done): Maybe[A] -⚬ Done =
      either(done, f)

    def switchWithL[A, B, R](
      caseNone: A -⚬ R,
      caseJust: (A |*| B) -⚬ R,
    ): (A |*| Maybe[B]) -⚬ R =
      distributeL > either(elimSnd > caseNone, caseJust)

    def switchWithR[A, B, R](
      caseNone: B -⚬ R,
      caseJust: (A |*| B) -⚬ R,
    ): (Maybe[A] |*| B) -⚬ R =
      distributeR > either(elimFst > caseNone, caseJust)

    given monadMaybe: Monad[Maybe] =
      new Monad[Maybe] {
        override val category: Category[-⚬] =
          dsl.category

        override def lift[A, B](f: A -⚬ B): Maybe[A] -⚬ Maybe[B] =
          |+|.bimap(id[One], f)

        override def flatten[A]: Maybe[Maybe[A]] -⚬ Maybe[A] =
          either(injectL, id[Maybe[A]])

        override def pure[A]: A -⚬ Maybe[A] =
          injectR
      }

    extension [A](ma: $[Maybe[A]])(using LambdaContext) {
      def getOrElse(using pos: SourcePos)(ifEmpty: One -⚬ A): $[A] =
        Maybe.getOrElse(ifEmpty)(ma)(using pos)
    }
  }

  opaque type Optionally[A] = One |&| A
  object Optionally {
    def optOut[A]: Optionally[A] -⚬ One =
      chooseL

    def optIn[A]: Optionally[A] -⚬ A =
      chooseR

    def fromChoice[A]: (One |&| A) -⚬ Optionally[A] =
      id

    def fromDiscardable[A](discard: A -⚬ One): A -⚬ Optionally[A] =
      choice(discard, id)

    def fromAffine[A](using A: Affine[A]): A -⚬ Optionally[A] =
      fromDiscardable(A.discard)

    def apply[A](using SourcePos, LambdaContext)(a: $[A])(using A: Affine[A]): $[Optionally[A]] =
      fromAffine[A](a) match
        case ?(oa) => oa

    extension [A](a: $[Optionally[A]])
      def get(using SourcePos, LambdaContext): $[A] =
        optIn(a)

    given Functor[Optionally] with {
      override val category = dsl.category

      override def lift[A, B](f: A -⚬ B): Optionally[A] -⚬ Optionally[B] =
        choice(optOut, optIn > f)
    }

    given affine[A]: Affine[Optionally[A]] with {
      override def discard: Optionally[A] -⚬ One =
        optOut[A]
    }
  }

  opaque type PMaybe[A] = Done |+| A
  object PMaybe {
    def empty[A]: Done -⚬ PMaybe[A] =
      injectL

    def just[A]: A -⚬ PMaybe[A] =
      injectR

    def fromEither[A]: (Done |+| A) -⚬ PMaybe[A] =
      id

    def toEither[A]: PMaybe[A] -⚬ (Done |+| A) =
      id

    def switch[A, R](
      caseNone: Done -⚬ R,
      caseSome: A -⚬ R,
    ): PMaybe[A] -⚬ R =
      either(caseNone, caseSome)

    def switchWithL[A, B, R](
      caseNone: (A |*| Done) -⚬ R,
      caseSome: (A |*| B) -⚬ R,
    ): (A |*| PMaybe[B]) -⚬ R =
      distributeL > either(caseNone, caseSome)

    def switchWithR[A, B, R](
      caseNone: (Done |*| B) -⚬ R,
      caseSome: (A |*| B) -⚬ R,
    ): (PMaybe[A] |*| B) -⚬ R =
      distributeR > either(caseNone, caseSome)

    def getOrElse[A](f: Done -⚬ A): PMaybe[A] -⚬ A =
      either(f, id)

    def neglect[A](f: A -⚬ Done): PMaybe[A] -⚬ Done =
      either(id, f)

    def neglect[A](using A: CloseableCosemigroup[A]): PMaybe[A] -⚬ Done =
      neglect(A.close)

    def lift[A, B](f: A -⚬ B): PMaybe[A] -⚬ PMaybe[B] =
      Bifunctor[|+|].lift(id, f)
  }

  def parFromOne[A, B](f: One -⚬ A, g: One -⚬ B): One -⚬ (A |*| B) =
    introSnd[One] > par(f, g)

  def parToOne[A, B](f: A -⚬ One, g: B -⚬ One): (A |*| B) -⚬ One =
    par(f, g) > elimSnd[One]

  private type MultipleF[A, X] = One |+| (A |+| (X |*| X))

  /** Zero or more instances of `A`. The exact multiplicity is determined by the producer.
    *
    * Similar to [[LList]], but unlike [[LList]], the producer of [[Multiple]] is not required to unveil
    * the elements sequentially. There are many different representations (in fact an infinite number)
    * of the same sequence of elements of type `A` as `Multiple[A]`, while there is only one representation
    * of that sequence as `LList[A]`.
    */
  opaque type Multiple[A] = Rec[MultipleF[A, *]]
  object Multiple {
    def zero[A]: One -⚬ Multiple[A] =
      injectL > pack[MultipleF[A, *]]

    def one[A]: A -⚬ Multiple[A] =
      injectL > injectR > pack[MultipleF[A, *]]

    def append[A]: (Multiple[A] |*| Multiple[A]) -⚬ Multiple[A] =
      injectR > injectR > pack[MultipleF[A, *]]

    def switch[A, R](
      case0: One -⚬ R,
      case1: A -⚬ R,
      caseN: (Multiple[A] |*| Multiple[A]) -⚬ R,
    ): Multiple[A] -⚬ R =
      unpack[MultipleF[A, *]] > either(case0, either(case1, caseN))

    def map[A, B](f: A -⚬ B): Multiple[A] -⚬ Multiple[B] = rec { self =>
      switch(
        case0 = zero,
        case1 = f > one,
        caseN = par(self, self) > append,
      )
    }

    def flatten[A]: Multiple[Multiple[A]] -⚬ Multiple[A] = rec { self =>
      switch(
        case0 = zero,
        case1 = id,
        caseN = par(self, self) > append
      )
    }

    given [A]: Monoid[Multiple[A]] with {
      def unit    :                           One -⚬ Multiple[A] = Multiple.zero
      def combine : (Multiple[A] |*| Multiple[A]) -⚬ Multiple[A] = Multiple.append
    }

    given Monad[Multiple] with {
      override val category: Category[-⚬] =
        dsl.category

      override def lift[A, B](f: A -⚬ B): Multiple[A] -⚬ Multiple[B] =
        Multiple.map(f)

      override def pure[A]: A -⚬ Multiple[A] =
        Multiple.one

      override def flatten[A]: Multiple[Multiple[A]] -⚬ Multiple[A] =
        Multiple.flatten
    }
  }

  private type UnlimitedF[A, X] = One |&| (A |&| (X |*| X))

  /** Unlimited supply of `A`s. The consumer chooses how many `A`s to consume. */
  opaque type Unlimited[A] = Rec[UnlimitedF[A, *]]
  object Unlimited {
    def apply[A](using SourcePos, LambdaContext)(a: $[A])(using Comonoid[A]): $[Unlimited[A]] =
      fromComonoid[A](a) match
        case *(ua) => ua

    private def unpack[A]: Unlimited[A] -⚬ UnlimitedF[A, Unlimited[A]] =
      dsl.unpack

    def fromChoice[A]: (One |&| (A |&| (Unlimited[A] |*| Unlimited[A]))) -⚬ Unlimited[A] =
      dsl.pack[UnlimitedF[A, *]]

    def toChoice[A]: Unlimited[A] -⚬ (One |&| (A |&| (Unlimited[A] |*| Unlimited[A]))) =
      unpack

    def discard[A]: Unlimited[A] -⚬ One =
      unpack > chooseL

    def single[A]: Unlimited[A] -⚬ A =
      unpack > chooseR > chooseL

    def split[A]: Unlimited[A] -⚬ (Unlimited[A] |*| Unlimited[A]) =
      unpack > chooseR > chooseR

    def getFst[A]: Unlimited[A] -⚬ (A |*| Unlimited[A]) =
      split > fst(single)

    def getSnd[A]: Unlimited[A] -⚬ (Unlimited[A] |*| A) =
      split > snd(single)

    def getSome[A]: Unlimited[A] -⚬ (A |*| Unlimited[A]) =
      getFst[A]

    def create[X, A](
      case0: X -⚬ One,
      case1: X -⚬ A,
      caseN: X -⚬ (Unlimited[A] |*| Unlimited[A]),
    ): X -⚬ Unlimited[A] =
      choice(case0, choice(case1, caseN)) > pack[UnlimitedF[A, *]]

    def createWith[X, A, Y](
      case0: X -⚬ Y,
      case1: X -⚬ (A |*| Y),
      caseN: X -⚬ ((Unlimited[A] |*| Unlimited[A]) |*| Y),
    ): X -⚬ (Unlimited[A] |*| Y) =
      choice(case0 > introFst, choice(case1, caseN) > coDistributeR) > coDistributeR > par(pack[UnlimitedF[A, *]], id)

    def createWith[X: Cosemigroup, A, Y: Semigroup](
      case0: X -⚬ Y,
      case1: X -⚬ (A |*| Y),
    ): X -⚬ (Unlimited[A] |*| Y) = rec { self =>
      createWith[X, A, Y](
        case0 = case0,
        case1 = case1,
        caseN = summon[Cosemigroup[X]].split > par(self, self) > IXI > snd(summon[Semigroup[Y]].combine),
      )
    }

    def fromComonoid[A](using A: Comonoid[A]): A -⚬ Unlimited[A] = rec { self =>
      create(
        case0 = A.discard,
        case1 = id[A],
        caseN = A.split > par(self, self),
      )
    }

    def duplicate[A]: Unlimited[A] -⚬ Unlimited[Unlimited[A]] = rec { self =>
      create(
        case0 = discard,
        case1 = id,
        caseN = split > par(self, self)
      )
    }

    def map[A, B](f: A -⚬ B): Unlimited[A] -⚬ Unlimited[B] = rec { self =>
      create(
        case0 = discard,
        case1 = single[A] > f,
        caseN = split[A] > par(self, self),
      )
    }

    def zip[A, B]: (Unlimited[A] |*| Unlimited[B]) -⚬ Unlimited[A |*| B] = rec { self =>
      create(
        case0 = parToOne(discard[A], discard[B]),
        case1 = par(single[A], single[B]),
        caseN = par(split[A], split[B]) > IXI > par(self, self),
      )
    }

    def unfold[S, A](f: S -⚬ (A |*| S)): S -⚬ (Unlimited[A] |*| S) =
      id                                     [                  S ]
        ./>(Endless.unfold(f))            .to[  Endless[A]  |*| S ]
        ./>.fst(Endless.toUnlimited[A])   .to[ Unlimited[A] |*| S ]

    def discardWhenDone[A]: (Done |*| Unlimited[A]) -⚬ Done =
      snd(unpack) > chooseLWhenDone > elimSnd

    def singleWhenDone[A]: (Done |*| Unlimited[A]) -⚬ (Done |*| A) =
      snd(unpack) > chooseRWhenDone > snd(chooseL)

    def splitWhenDone[A]: (Done |*| Unlimited[A]) -⚬ (Done |*| (Unlimited[A] |*| Unlimited[A])) =
      snd(unpack) > chooseRWhenDone > snd(chooseR)

    def getFstWhenDone[A]: (Done |*| Unlimited[A]) -⚬ (Done |*| (A |*| Unlimited[A])) =
      splitWhenDone > snd(fst(single))

    def getSndWhenDone[A]: (Done |*| Unlimited[A]) -⚬ (Done |*| (Unlimited[A] |*| A)) =
      splitWhenDone > snd(snd(single))

    /** Present a non-empty list of resources `A` as an unlimited supply of "borrowed" resources `A ⊗ Ā`,
      * where `Ā` is the dual of `A`. A borrowed resource `A ⊗ Ā` must be "returned" by "annihilating"
      * `A` and its dual `Ā`, namely via an inversion on the right `A ⊗ Ā -⚬ One`.
      * A returned resource will become available for further use when it signals readiness using the
      * [[Signaling.Positive]] instance.
      *
      * When all accesses to the pooled resources (obtained via the `Unlimited[A |*| Ā]` in the first
      * out-port) are closed, the resources are returned in the second out-port.
      */
    def poolBy[A: Signaling.Positive, Ā](
      lInvert: One -⚬ (Ā |*| A),
    ): LList1[A] -⚬ (Unlimited[A |*| Ā] |*| LList1[A]) =
      unfold(LList1.borrow(lInvert))

    def pool[A](using Signaling.Positive[A]): LList1[A] -⚬ (Unlimited[A |*| -[A]] |*| LList1[A]) =
      Unlimited.poolBy[A, -[A]](forevert[A])

    given comonoidUnlimited[A]: Comonoid[Unlimited[A]] with {
      def counit : Unlimited[A] -⚬ One                             = Unlimited.discard
      def split  : Unlimited[A] -⚬ (Unlimited[A] |*| Unlimited[A]) = Unlimited.split
    }

    given Comonad[Unlimited] with {
      override val category: Category[-⚬] =
        dsl.category

      override def lift[A, B](f: A -⚬ B): Unlimited[A] -⚬ Unlimited[B] =
        Unlimited.map(f)

      override def extract[A]: Unlimited[A] -⚬ A =
        Unlimited.single

      override def duplicate[A]: Unlimited[A] -⚬ Unlimited[Unlimited[A]] =
        Unlimited.duplicate
    }

    /** Signals when the choice is made between [[discard]], [[single]] and [[split]]. */
    given signalingUnlimited[A]: Signaling.Negative[Unlimited[A]] = {
      val notifyFst: (Pong |*| Unlimited[A]) -⚬ Unlimited[A] =
        par(id, unpack) > notifyChoiceAndRight > pack[UnlimitedF[A, *]]

      Signaling.Negative.from(notifyFst)
    }

    given deferrableUnlimited[A]: Deferrable.Negative[Unlimited[A]] with {
      override def awaitPongFst: Unlimited[A] -⚬ (Pong |*| Unlimited[A]) =
        unpack > delayChoiceUntilPong > snd(pack[UnlimitedF[A, *]])
    }

    def toOptionally[A]: Unlimited[A] -⚬ Optionally[A] =
      unpack > |&|.rmap(chooseL) > Optionally.fromChoice

    extension [A](a: $[Unlimited[A]]) {
      def optionally(using SourcePos, LambdaContext): $[Optionally[A]] =
        import Optionally.affine
        toOptionally(a) match { case ?(oa) => oa }
    }
  }

  private type PUnlimitedF[A, X] = Done |&| (A |&| (X |*| X))
  opaque type PUnlimited[A] = Rec[PUnlimitedF[A, *]]
  object PUnlimited {
    def neglect[A]: PUnlimited[A] -⚬ Done =
      unpack[PUnlimitedF[A, *]] > chooseL

    def single[A]: PUnlimited[A] -⚬ A =
      unpack[PUnlimitedF[A, *]] > chooseR > chooseL

    def split[A]: PUnlimited[A] -⚬ (PUnlimited[A] |*| PUnlimited[A]) =
      unpack[PUnlimitedF[A, *]] > chooseR > chooseR

    def getFst[A]: PUnlimited[A] -⚬ (A |*| PUnlimited[A]) =
      split > fst(single)

    def getSnd[A]: PUnlimited[A] -⚬ (PUnlimited[A] |*| A) =
      split > snd(single)

    def create[X, A](
      case0: X -⚬ Done,
      case1: X -⚬ A,
      caseN: X -⚬ (PUnlimited[A] |*| PUnlimited[A]),
    ): X -⚬ PUnlimited[A] =
      choice(case0, choice(case1, caseN)) > pack[PUnlimitedF[A, *]]

    def createWith[X, A, Y](
      case0: X -⚬ (Done |*| Y),
      case1: X -⚬ (A |*| Y),
      caseN: X -⚬ ((PUnlimited[A] |*| PUnlimited[A]) |*| Y),
    ): X -⚬ (PUnlimited[A] |*| Y) =
      choice(case0, choice(case1, caseN) > coDistributeR) > coDistributeR > par(pack[PUnlimitedF[A, *]], id)

    def map[A, B](f: A -⚬ B): PUnlimited[A] -⚬ PUnlimited[B] = rec { self =>
      create(
        case0 = neglect,
        case1 = single > f,
        caseN = split > par(self, self)
      )
    }

    def duplicate[A]: PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] = rec { self =>
      create(
        case0 = neglect,
        case1 = id,
        caseN = split > par(self, self)
      )
    }

    given closeableCosemigroupPUnlimited[A]: CloseableCosemigroup[PUnlimited[A]] =
      new CloseableCosemigroup[PUnlimited[A]] {
        def close : PUnlimited[A] -⚬ Done                              = PUnlimited.neglect
        def split : PUnlimited[A] -⚬ (PUnlimited[A] |*| PUnlimited[A]) = PUnlimited.split
      }

    given comonadPUnlimited: Comonad[PUnlimited] =
      new Comonad[PUnlimited] {
        override val category: Category[-⚬] =
          dsl.category

        override def lift[A, B](f: A -⚬ B): PUnlimited[A] -⚬ PUnlimited[B] =
          PUnlimited.map(f)

        override def extract[A]: PUnlimited[A] -⚬ A =
          PUnlimited.single

        override def duplicate[A]: PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] =
          PUnlimited.duplicate
      }
  }

  trait NAffine[A] {
    def deflate: A -⚬ Need
  }

  object NAffine {
    def from[A](f: A -⚬ Need): NAffine[A] =
      new NAffine[A] {
        override def deflate: A -⚬ Need =
          f
      }

    given NAffine[Need] =
      from(id)

    given [A, B](using A: NAffine[A], B: NAffine[B]): NAffine[A |*| B] =
      from(par(A.deflate, B.deflate) > forkNeed)
  }

  trait Closeable[A] {
    def close: A -⚬ Done
  }

  object Closeable {
    def from[A](f: A -⚬ Done): Closeable[A] =
      new Closeable[A] {
        override def close: A -⚬ Done =
          f
      }

    given fromAffine[A](using A: Affine[A]): Closeable[A] =
      from(A.discard > done)

    given closeableDone: Closeable[Done] =
      from(id)

    given closeablePing: Closeable[Ping] =
      from(strengthenPing)

    given closeablePair[A, B](using A: Closeable[A], B: Closeable[B]): Closeable[A |*| B] =
      from(par(A.close, B.close) > join)

    given closeableEither[A, B](using A: Closeable[A], B: Closeable[B]): Closeable[A |+| B] =
      from(either(A.close, B.close))
  }

  trait Semigroup[A] {
    def combine: (A |*| A) -⚬ A

    def law_associativity: Equal[ ((A |*| A) |*| A) -⚬ A ] =
      Equal(
        par(combine, id[A]) > combine,
        assocLR > par(id[A], combine) > combine,
      )
  }

  object Semigroup {
    given Semigroup[Done] with {
      override def combine: (Done |*| Done) -⚬ Done = join
    }

    given Semigroup[Ping] with {
      override def combine: (Ping |*| Ping) -⚬ Ping = joinPing
    }

    given Semigroup[Need] with {
      override def combine: (Need |*| Need) -⚬ Need = forkNeed
    }

    given Semigroup[Pong] with {
      override def combine: (Pong |*| Pong) -⚬ Pong = forkPong
    }
  }

  def combine[A: Semigroup]: (A |*| A) -⚬ A =
    summon[Semigroup[A]].combine

  def combineMap[A, B, C: Semigroup](f: A -⚬ C, g: B -⚬ C): (A |*| B) -⚬ C =
    par(f, g) > combine[C]

  extension [A, C](f: A -⚬ C) {
    /** Combines the outputs of left and right operand. */
    def \/[B](g: B -⚬ C)(using Semigroup[C]): (A |*| B) -⚬ C =
      combineMap(f, g)
  }

  def split[A: Cosemigroup]: A -⚬ (A |*| A) =
    summon[Cosemigroup[A]].split

  def splitMap[A: Cosemigroup, B, C](f: A -⚬ B, g: A -⚬ C): A -⚬ (B |*| C) =
    split[A] > par(f, g)

  extension [A, B](f: A -⚬ B) {
    /** Splits the input and pipes the two halves to the left and right operand. */
    def /\[C](g: A -⚬ C)(using Cosemigroup[A]): A -⚬ (B |*| C) =
      splitMap(f, g)
  }

  trait Monoid[A] extends Semigroup[A] {
    def unit: One -⚬ A

    def law_leftUnit: Equal[ (One |*| A) -⚬ A ] =
      Equal(
        par(unit, id[A]) > this.combine,
        elimFst,
      )

    def law_rightUnit: Equal[ (A |*| One) -⚬ A ] =
      Equal(
        par(id[A], unit) > this.combine,
        elimSnd,
      )
  }

  object Monoid {
    given Monoid[One] with {
      override def unit   :           One -⚬ One = id
      override def combine: (One |*| One) -⚬ One = elimSnd[One]
    }

    given Monoid[Done] with {
      override def unit   :             One -⚬ Done = done
      override def combine: (Done |*| Done) -⚬ Done = join
    }

    given Monoid[Ping] with {
      override def unit   :             One -⚬ Ping = ping
      override def combine: (Ping |*| Ping) -⚬ Ping = joinPing
    }
  }

  /** A [[Monoid]] whose [[unit]] can be chained after a signal flowing in the '''P'''ositive direction ([[Done]]),
    * effectively taking on the responsibility to wait for completion of some computation.
    *
    * Its dual is [[NComonoid]].
    */
  trait PMonoid[A] extends Semigroup[A] {
    def unit: Done -⚬ A

    def monoid: Monoid[A] = new Monoid[A] {
      def combine: (A |*| A) -⚬ A = PMonoid.this.combine
      def unit: One -⚬ A = done > PMonoid.this.unit
    }

    def law_leftUnit: Equal[ (One |*| A) -⚬ A ] =
      Equal(
        par(done > unit, id[A]) > this.combine,
        elimFst,
      )

    def law_rightUnit: Equal[ (A |*| One) -⚬ A ] =
      Equal(
        par(id[A], done > unit) > this.combine,
        elimSnd,
      )
  }

  /** A [[Comonoid]] whose [[counit]] can be chained before a signal flowing in the '''N'''egative direction ([[Need]]),
    * effectively taking on the responsibility to await completion of some computation.
    *
    * The dual of [[PMonoid]].
    */
  trait NComonoid[A] extends Cosemigroup[A]  with NAffine[A] {
    def counit: A -⚬ Need

    override def deflate: A -⚬ Need =
      counit

    def comonoid: Comonoid[A] = new Comonoid[A] {
      def split: A -⚬ (A |*| A) = NComonoid.this.split
      def counit: A -⚬ One = NComonoid.this.counit > need
    }

    def law_leftCounit: Equal[ A -⚬ (One |*| A) ] =
      Equal(
        this.split > par(counit > need, id[A]),
        introFst,
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| One) ] =
      Equal(
        this.split > par(id[A], counit > need),
        introSnd,
      )
  }

  /** A weaker version of [[Monoid]] whose [[unit]] creates a liability - a signal traveling in the '''N'''egative
    * direction ([[Need]]) that eventually needs to be awaited.
    *
    * Its dual is [[PComonoid]].
    */
  trait NMonoid[A] extends Semigroup[A] {
    def unit: Need -⚬ A

    def law_leftUnit: Equal[ (LTerminus |*| A) -⚬ A ] =
      Equal(
        par(regressInfinitely > unit, id[A]) > this.combine,
        id[LTerminus |*| A] > elimFst(regressInfinitely > need),
      )

    def law_rightUnit: Equal[ (A |*| LTerminus) -⚬ A ] =
      Equal(
        par(id[A], regressInfinitely > unit) > this.combine,
        id[A |*| LTerminus] > elimSnd(regressInfinitely > need),
      )
  }

  object NMonoid {
    given NMonoid[Need] with {
      override def combine : (Need |*| Need) -⚬ Need = forkNeed
      override def unit    :            Need -⚬ Need = id
    }
  }

  /** A weaker version of [[Comonoid]] where the input cannot be discarded completely, but can be reduced to
    * a signal traveling in the positive direction ([[Done]]) that eventually needs to be awaited.
    *
    * The dual of [[NMonoid]].
    */
  trait CloseableCosemigroup[A] extends Cosemigroup[A] with Closeable[A] {
    def law_leftCounit: Equal[ A -⚬ (RTerminus |*| A) ] =
      Equal(
        this.split > par(close > delayIndefinitely, id[A]),
        id[A] > introFst(done > delayIndefinitely),
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| RTerminus) ] =
      Equal(
        this.split > par(id[A], close > delayIndefinitely),
        id[A] > introSnd(done > delayIndefinitely),
      )
  }

  object CloseableCosemigroup {
    given closeableCosemigroupDone: CloseableCosemigroup[Done] with {
      override def split : Done -⚬ (Done |*| Done) = fork
      override def close : Done -⚬ Done            = id
    }
  }

  type Monad[F[_]] =
    libretto.cats.Monad[-⚬, F]

  type Comonad[F[_]] =
    libretto.cats.Comonad[-⚬, F]

  def getFst[A, B](using A: Cosemigroup[A]): (A |*| B) -⚬ (A |*| (A |*| B)) =
    id                             [     A     |*| B  ]
      ./>.fst(A.split)          .to[ (A |*| A) |*| B  ]
      ./>(assocLR)              .to[  A |*| (A |*| B) ]

  def getSnd[A, B](using B: Cosemigroup[B]): (A |*| B) -⚬ (B |*| (A |*| B)) =
    id                             [  A |*|     B     ]
      ./>.snd(B.split)          .to[  A |*| (B |*| B) ]
      ./>(assocRL)              .to[ (A |*| B) |*| B  ]
      ./>(swap)                 .to[  B |*| (A |*| B) ]

  def discardFst[A, B](using A: Comonoid[A]): (A |*| B) -⚬ B =
    elimFst(A.counit)

  def discardSnd[A, B](using B: Comonoid[B]): (A |*| B) -⚬ A =
    elimSnd(B.counit)

  private type LListF[T, X] = One |+| (T |*| X)
  opaque type LList[T] = Rec[LListF[T, *]]

  object LList {
    def Nil[T] : Extractor[-⚬, |*|, LList[T],   One         ] = InL.afterUnpack
    def Cons[T]: Extractor[-⚬, |*|, LList[T], T |*| LList[T]] = InR.afterUnpack

    private def unpack[T]: LList[T] -⚬ LListF[T, LList[T]] = dsl.unpack
    private def pack[T]  : LListF[T, LList[T]] -⚬ LList[T] = dsl.pack

    def nil[T]: One -⚬ LList[T] =
      Nil[T].reinject

    def cons[T]: (T |*| LList[T]) -⚬ LList[T] =
      Cons[T].reinject

    def singleton[T]: T -⚬ LList[T] =
      λ { t => Cons(t |*| Nil($.one)) }

    def uncons[T]: LList[T] -⚬ (One |+| (T |*| LList[T])) =
      unpack

    /** Signals when it is decided whether the list is empty (nil) or has an element (cons). */
    given [T]: Signaling.Positive[LList[T]] =
      Signaling.Positive.from(unpack > notifyEither > par(id, pack))

    def fromList0[S, T](fs: List[S -⚬ T])(using S: Cosemigroup[S]): S -⚬ (S |*| LList[T]) = {
      @tailrec def go(rfs: List[S -⚬ T], acc: S -⚬ (S |*| LList[T])): S -⚬ (S |*| LList[T]) =
        rfs match {
          case head :: tail => go(tail, S.split > par(id, acc > par(head, id) > cons))
          case scala.Nil => acc
        }

      go(fs.reverse, id[S] > introSnd(nil[T]))
    }

    def fromList[S, T](fs: List[S -⚬ T])(using S: Comonoid[S]): S -⚬ LList[T] =
      fromList0(fs) > discardFst

    def fromListU[S, T](fs: List[S -⚬ T]): Unlimited[S] -⚬ LList[T] = {
      import Unlimited.given

      fromList(fs map (Unlimited.single > _))
    }

    def of[S, T](fs: (S -⚬ T)*)(using S: Comonoid[S]): S -⚬ LList[T] =
      fromList(fs.toList)

    def unfold[S, T](f: S -⚬ (One |+| (T |*| S))): S -⚬ LList[T] =
      λ.rec { self => s =>
        switch ( f(s) )
          .is { case InL(u) => Nil(u) }
          .is { case InR(t |*| s) => Cons(t |*| self(s)) }
          .end
      }

    def fill[S, T](n: Int)(f: S -⚬ T)(using Comonoid[S]): S -⚬ LList[T] = {
      require(n >= 0, s"n must be non-negative, was $n")
      fromList(List.fill(n)(f))
    }

    def fill0[S, T](n: Int)(f: S -⚬ T)(using Cosemigroup[S]): S -⚬ (S |*| LList[T]) = {
      require(n >= 0, s"n must be non-negative, was $n")
      fromList0(List.fill(n)(f))
    }

    @deprecated("Use pattern matching")
    def switchWithL[A, T, R](
      caseNil: A -⚬ R,
      caseCons: (A |*| (T |*| LList[T])) -⚬ R,
    ): (A |*| LList[T]) -⚬ R =
      par(id, uncons[T]) > distributeL > either(elimSnd > caseNil, caseCons)

    def map[T, U](f: T -⚬ U): LList[T] -⚬ LList[U] =
      λ.rec { self => ts =>
        switch(ts)
          .is { case Nil(u)         => Nil(u) }
          .is { case Cons(t |*| ts) => Cons(f(t) |*| self(ts)) }
          .end
      }

    def flatMapConcat[A, B](f: A -⚬ LList[B]): LList[A] -⚬ LList[B] =
      λ.rec { self => as =>
        switch(as)
          .is { case Nil(u)         => Nil(u) }
          .is { case Cons(a |*| as) => concat(f(a) |*| self(as)) }
          .end
      }

    def flatMapMerge[A, B](f: A -⚬ LList[B]): LList[A] -⚬ LList[B] =
      λ.rec { self => as =>
        switch(as)
          .is { case Nil(u)         => Nil(u) }
          .is { case Cons(a |*| as) => merge(f(a) |*| self(as)) }
          .end
      }

    /** Alias for [[flatMapConcat]]. */
    def flatMap[A, B](f: A -⚬ LList[B]): LList[A] -⚬ LList[B] =
      flatMapConcat(f)

    def mapS[S, T, U](f: (S |*| T) -⚬ (S |*| U)): (S |*| LList[T]) -⚬ (S |*| LList[U]) =
      λ.rec { self => { case s |*| ts =>
        switch(ts)
          .is { case Nil(u) =>
            s |*| Nil(u)
          }
          .is { case Cons(t |*| ts) =>
            val s1 |*| u  = f(s |*| t)
            val s2 |*| us = self(s1 |*| ts)
            s2 |*| Cons(u |*| us)
          }
          .end
      }}

    def mapSAppend[S, T, U](f: (S |*| T) -⚬ (S |*| U), tail: S -⚬ LList[U]): (S |*| LList[T]) -⚬ LList[U] =
      λ.rec { self => { case s |*| ts =>
        switch(ts)
          .is { case Nil(?(_)) => tail(s) }
          .is { case Cons(t |*| ts) =>
            val s1 |*| u  = f(s |*| t)
            val us = self(s1 |*| ts)
            Cons(u |*| us)
          }
          .end
      }}

    def foldMap0[T, U](f: T -⚬ U)(using U: Semigroup[U]): LList[T] -⚬ Maybe[U] =
      λ { ts =>
        switch(ts)
          .is { case Nil(u) => Maybe.empty[U](u) }
          .is { case Cons(t |*| ts) => Maybe.just(foldL[U, T](snd(f) > U.combine)(f(t) |*| ts)) }
          .end
      }

    def foldMap[T, U](f: T -⚬ U)(using U: Monoid[U]): LList[T] -⚬ U =
      λ.rec { self => ts =>
        switch(ts)
          .is { case Nil(u) => U.unit(u) }
          .is { case Cons(t |*| ts) => U.combine(f(t) |*| self(ts)) }
          .end
      }

    def fold0[T](using T: Semigroup[T]): LList[T] -⚬ Maybe[T] =
      foldMap0(id[T])

    def fold[T](using T: Monoid[T]): LList[T] -⚬ T =
      foldMap(id[T])

    def foldL[S, T](f: (S |*| T) -⚬ S): (S |*| LList[T]) -⚬ S =
      λ.rec { self => { case s |*| ts =>
        switch(ts)
          .is { case Nil(?(_))      => s }
          .is { case Cons(t |*| ts) => self(f(s |*| t) |*| ts) }
          .end
      }}

    def concat[T]: (LList[T] |*| LList[T]) -⚬ LList[T] =
      λ.rec { self => { case xs |*| ys =>
        switch(xs)
          .is { case Nil(?(_))      => ys }
          .is { case Cons(x |*| xs) => Cons(x |*| self(xs |*| ys)) }
          .end
      }}

    def partition[A, B]: LList[A |+| B] -⚬ (LList[A] |*| LList[B]) =
      λ.rec { self => xs =>
        switch(xs)
          .is { case Nil(?(_)) => constant(nil[A]) |*| constant(nil[B]) }
          .is { case Cons(x |*| t) =>
            val as |*| bs = self(t)
            switch ( x )
              .is { case InL(a) => cons(a |*| as) |*| bs }
              .is { case InR(b) => as |*| cons(b |*| bs) }
              .end
          }
          .end
      }

    def consMaybe[T]: (Maybe[T] |*| LList[T]) -⚬ LList[T] =
      id[Maybe[T] |*| LList[T]]             .to[ (One |+|                T) |*| LList[T] ]
        .>(distributeR)                     .to[ (One |*| LList[T]) |+| (T |*| LList[T]) ]
        .>(either(elimFst, cons))           .to[                 LList[T]                ]

    def collect[T, U](f: T -⚬ Maybe[U]): LList[T] -⚬ LList[U] =
      λ.rec { self => ts =>
        switch(ts)
          .is { case Nil(u) => Nil(u) }
          .is { case Cons(t |*| ts) => consMaybe(f(t) |*| self(ts)) }
          .end
      }

    def transform[T, A, U](f: (A |*| T) -⚬ U)(using A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
      rec { self =>
        val caseNil: A -⚬ LList[U] =
          A.discard > nil[U]
        val caseCons: (A |*| (T |*| LList[T])) -⚬ LList[U] =
          par(A.split, id) > IXI > par(f, self) > cons[U]
        switchWithL(caseNil, caseCons)
      }

    def transform0[T, A, U](f: (A |*| T) -⚬ U)(using Cosemigroup[A]): (A |*| LList[T]) -⚬ (A |*| LList[U]) = {
      def go: (A |*| (T |*| LList[T])) -⚬ LList[U] =
        rec { go =>
          assocRL > switchWithL(
            f > singleton,
            λ { case (+(a) |*| t0) |*| ts1 =>
              cons(f(a |*| t0) |*| go(a |*| ts1))
            },
          )
        }

      switchWithL(
        introSnd(nil[U]),
        λ { case (+(a) |*| ts1) => a |*| go(a |*| ts1) }
      )
    }

    def transform1[T, A, U](f: (A |*| T) -⚬ U)(using Cosemigroup[A]): (A |*| LList[T]) -⚬ (A |+| LList1[U]) =
      switchWithL(
        injectL,
        snd(LList1.cons) > LList1.transform(f) > injectR,
      )

    def transformCollect[T, A, U](f: (A |*| T) -⚬ Maybe[U])(using A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
      rec { self =>
        val caseNil: A -⚬ LList[U] =
          A.discard > nil[U]
        val caseCons: (A |*| (T |*| LList[T])) -⚬ LList[U] =
          par(A.split, id) > IXI > par(f, self) > consMaybe[U]
        switchWithL(caseNil, caseCons)
      }

    def unzip[A, B]: LList[A |*| B] -⚬ (LList[A] |*| LList[B]) =
      λ.rec { self => xs =>
        switch(xs)
          .is { case Nil(*(u)) => Nil(u) |*| Nil(u) }
          .is { case Cons((a |*| b) |*| xs) =>
            val as |*| bs = self(xs)
            Cons(a |*| as) |*| Cons(b |*| bs)
          }
          .end
      }

    def splitAt[A](i: Int): LList[A] -⚬ (LList[A] |*| LList[A]) = {
      require(i >= 0, s"i must not be negative, was $i")
      if (i == 0)
        introFst(LList.nil[A])
      else
        uncons > either(
          parFromOne(LList.nil[A], LList.nil[A]),
          snd(splitAt(i-1)) > assocRL > fst(cons),
        )
    }

    def splitEvenOdd[A]: LList[A] -⚬ (LList[A] |*| LList[A]) =
      λ.rec { self => as =>
        switch(as)
          .is { case Nil(*(u))          => Nil(u) |*| Nil(u) }
          .is { case Cons(a |*| Nil(u)) => singleton[A](a) |*| Nil(u) }
          .is { case Cons(a0 |*| Cons(a1 |*| as)) =>
            val as0 |*| as1 = self(as)
            Cons(a0 |*| as0) |*| Cons(a1 |*| as1)
          }
          .end
      }

    private def waveL[A, S, B](
      init: A -⚬ S,
      f: (S |*| A) -⚬ (B |*| S),
      last: S -⚬ B,
    ): LList[A] -⚬ LList[B] =
      λ { as =>
        switch(as)
          .is { case Nil(u) => Nil(u) }
          .is { case Cons(a |*| as) =>
            val s0 = init(a)
            mapSAppend(f > swap, last > singleton)(s0 |*| as)
          }
          .end
      }

    /** Shifts all the elements of a list by "half" to the left,
     *  moving the first half of the first element to the end of the list.
     *
     *  Example:
     *
     *  Before:
     *  ```
     *  (a1, b1), (a2, b2), (a3, b3)
     *  ```
     *
     *  After:
     *  ```
     *  (b1, a2), (b2, a3), (b3, a1)
     *  ```
     */
    def halfRotateL[A, B]: LList[A |*| B] -⚬ LList[B |*| A] = {
      val f: ((B |*| A) |*| (A |*| B)) -⚬ ((B |*| A) |*| (B |*| A)) =
        IXI > snd(swap)

      waveL[A |*| B, B |*| A, B |*| A](
        init = swap,
        f    = f,
        last = id,
      )
    }

    /** Creates a singleton list that will appear as undecided (between nil and cons)
     *  until the element signals.
     */
    def singletonOnSignal[T](using T: Signaling.Positive[T]): T -⚬ LList[T] =
      id                                   [            T                ]
        .>(T.notifyPosFst)              .to[  Ping |*|  T                ]
        .>(par(id, introSnd(nil[T])))   .to[  Ping |*| (T  |*| LList[T]) ]
        .>(injectROnPing)               .to[   One |+| (T  |*| LList[T]) ]
        .>(pack)                        .to[     LList[T]                ]

    /** Merges the two lists as they unfold, i.e. as soon as the next element becomes available in one of the lists,
     *  it also becomes available as the next element of the result list.
     */
    def merge[T]: (LList[T] |*| LList[T]) -⚬ LList[T] = λ.rec { self =>
      { case as |*| bs =>
        switch ( race(as |*| bs) )
          .is { case InL(as |*| bs) =>
            dsl.switch ( uncons(as) )
              .is { case InL(?(one))   => bs }
              .is { case InR(a |*| as) => cons(a |*| self(as |*| bs)) }
              .end
          }
          .is { case InL(as |*| bs) =>
            dsl.switch ( uncons(bs) )
              .is { case InL(?(one)) => as }
              .is { case InR(b |*| bs) => cons(b |*| self(as |*| bs)) }
              .end
          }
          .end
      }
    }

    /** Inserts an element to a list as soon as the element signals.
     *  If _m_ elements of the input list become available before the new element signals,
     *  the new element will appear as the _(m+1)_-th element in the output list.
     *  Note: The _m_ elements from the input list are not awaited to signal;
     *  their timely appearence in the input list is sufficient for them to come before
     *  the inserted element.
     */
    def insertBySignal[T](using Signaling.Positive[T]): (T |*| LList[T]) -⚬ LList[T] =
      λ.rec { self =>
        { case a |*| as =>
          switch ( race[T, LList[T]](a |*| as) )
            .is { case InL(a |*| as) =>
              cons(a |*| as)
            }
            .is { case InR(a |*| as) =>
              switch ( uncons(as) )
                .is { case InL(?(one))     => singletonOnSignal(a) }
                .is { case InR(a1 |*| as) => cons(a1 |*| self(a |*| as)) }
                .end
            }
            .end
        }
      }

    /** Make the elements of the input list available in the output list in the order in which they signal. */
    def sortBySignal[T](using Signaling.Positive[T]): LList[T] -⚬ LList[T] = rec { self =>
      // XXX O(n^2) complexity: if the element at the end of the list signals first, it will take O(n) steps for it
      // to bubble to the front. Could be improved to O(log(n)) steps to bubble any element and O(n*log(n)) total
      // complexity by using a heap data structure.
      λ { as =>
        dsl.switch ( uncons(as) )
          .is { case InL(one)      => nil(one) }
          .is { case InR(a |*| as) => insertBySignal(a |*| self(as)) }
          .end
      }
    }

    given [A]: Monoid[LList[A]] with {
      def unit    :                     One -⚬ LList[A] = nil
      def combine : (LList[A] |*| LList[A]) -⚬ LList[A] = concat
    }
  }

  /** Non-empty list, i.e. a list with at least one element. */
  opaque type LList1[T] = T |*| LList[T]
  object LList1 {
    def apply[T](x: $[T], xs: $[T]*)(using LambdaContext): $[LList1[T]] =
      fromExprList(x, xs.toList)

    def fromExprList[T](h: $[T], t: List[$[T]])(using LambdaContext): $[LList1[T]] =
      t match {
        case Nil => singleton(h)
        case (x :: xs) => cons1(h |*| fromExprList(x, xs))
      }

    def cons[T]: (T |*| LList[T]) -⚬ LList1[T] =
      id

    def toLList[T]: LList1[T] -⚬ LList[T] =
      LList.cons[T]

    def cons1[T]: (T |*| LList1[T]) -⚬ LList1[T] =
      par(id, toLList)

    def singleton[T]: T -⚬ LList1[T] =
      introSnd(LList.nil[T])

    def uncons[T]: LList1[T] -⚬ (T |*| LList[T]) =
      id

    def switch[T, R](
      case1: T -⚬ R,
      caseN: (T |*| LList1[T]) -⚬ R,
    ): LList1[T] -⚬ R =
      LList.switchWithL(case1, caseN)

    def from[S, T](head: S -⚬ T, tail: List[S -⚬ T])(using S: Cosemigroup[S]): S -⚬ LList1[T] =
      LList.fromList0(tail) > par(head, id) > cons

    def from[S, T](fs: NonEmptyList[S -⚬ T])(using S: Cosemigroup[S]): S -⚬ LList1[T] =
      from(fs.head, fs.tail)

    def of[S, T](head: S -⚬ T, tail: (S -⚬ T)*)(using S: Cosemigroup[S]): S -⚬ LList1[T] =
      from(head, tail.toList)

    def unfold[S, T](f: S -⚬ (T |*| Maybe[S])): S -⚬ LList1[T] =
      λ { s =>
        val (h |*| sOpt) = f(s)
        val tail: $[LList[T]] = LList.unfold[Maybe[S], T](Maybe.map(f))(sOpt)
        cons(h |*| tail)
      }

    def fill[S, T](n: Int)(f: S -⚬ T)(using Cosemigroup[S]): S -⚬ LList1[T] = {
      require(n >= 1, s"n must be positive, was $n")
      from(f, List.fill(n-1)(f))
    }

    def map[T, U](f: T -⚬ U): LList1[T] -⚬ LList1[U] =
      par(f, LList.map(f))

    def mapS[S, T, U](f: (S |*| T) -⚬ (S |*| U)): (S |*| LList1[T]) -⚬ (S |*| LList1[U]) =
      assocRL > fst(f > swap) > assocLR > snd(LList.mapS(f)) > XI

    def mapSAppend[S, T, U](f: (S |*| T) -⚬ (S |*| U), tail: S -⚬ LList[U]): (S |*| LList1[T]) -⚬ LList1[U] =
      assocRL > fst(f > swap) > assocLR > snd(LList.mapSAppend(f, tail))

    def foldMap[T, U](f: T -⚬ U)(using U: Semigroup[U]): LList1[T] -⚬ U =
      par(f, id) > LList.foldL[U, T](par(id, f) > U.combine)

    def fold[T](using T: Semigroup[T]): LList1[T] -⚬ T =
      LList.foldL[T, T](T.combine)

    def closeAll[T](using T: Closeable[T]): LList1[T] -⚬ Done =
      foldMap(T.close)

    def transform[T, A, U](f: (A |*| T) -⚬ U)(using A: Cosemigroup[A]): (A |*| LList1[T]) -⚬ LList1[U] =
      λ { case a |*| (t0 |*| ts) =>
        val a1 |*| us = LList.transform0(f)(a |*| ts)
        f(a1 |*| t0) |*| us
      }

    /** Shifts all the elements of a list by "half" to the left,
     *  moving the first half of the first element to the end of the list.
     *
     *  Example:
     *
     *  Before:
     *  ```
     *  (a1, b1), (a2, b2), (a3, b3)
     *  ```
     *
     *  After:
     *  ```
     *  (b1, a2), (b2, a3), (b3, a1)
     *  ```
     */
    def halfRotateL[A, B]: LList1[A |*| B] -⚬ LList1[B |*| A] = {
      val f: ((A |*| B) |*| (A |*| B)) -⚬ ((A |*| B) |*| (B |*| A)) =
        snd(swap) > IXI

      switch(
        case1 = swap > singleton[B |*| A],
        caseN = mapSAppend[A |*| B, A |*| B, B |*| A](f, swap[A, B] > LList.singleton),
      )
    }

    /** Inserts an element to a list as soon as the element signals.
     *  If _m_ elements of the input list become available before the new element signals,
     *  the new element will appear as the _(m+1)_-th element in the output list.
     *  Note: The _m_ elements from the input list are not awaited to signal;
     *  their timely appearence in the input list is sufficient for them to come before
     *  the inserted element.
     */
    def insertBySignal[T](using Signaling.Positive[T]): (T |*| LList[T]) -⚬ LList1[T] = {
      import LList.given

      raceSwitch(
        caseFstWins = cons[T],
        caseSndWins = LList.switchWithL(
          caseNil = singleton[T],
          caseCons = XI > par(id, LList.insertBySignal[T]),
        ),
      )
    }

    def sortBySignal[A](using Signaling.Positive[A]): LList1[A] -⚬ LList1[A] =
      λ { case a |*| as => insertBySignal(a |*| LList.sortBySignal(as)) }

    def unzip[A, B]: LList1[A |*| B] -⚬ (LList1[A] |*| LList1[B]) =
      switch(
        par(singleton, singleton),
        λ { case (a |*| b) |*| tail =>
          val as |*| bs = LList.unzip(LList.cons(tail))
          cons(a |*| as) |*| cons(b |*| bs)
        }
      )

    def unzipBy[T, A, B](f: T -⚬ (A |*| B)): LList1[T] -⚬ (LList1[A] |*| LList1[B]) =
      map(f) > unzip

    def borrow[A, Ā](
      lInvert: One -⚬ (Ā |*| A),
    )(using
      Signaling.Positive[A],
    ): LList1[A] -⚬ ((A |*| Ā) |*| LList1[A]) =
      λ { case a |*| as =>
        val na |*| a1 = constant(lInvert)
        (a |*| na) |*| insertBySignal(a1 |*| as)
      }

    def eachNotifyBy[A](notify: A -⚬ (Ping |*| A)): LList1[A] -⚬ (Ping |*| LList1[A]) =
      unzipBy(notify) > fst(fold)

    def eachNotify[A](using A: Signaling.Positive[A]): LList1[A] -⚬ (Ping |*| LList1[A]) =
      eachNotifyBy(A.notifyPosFst)

    def eachAwaitBy[A](await: (Done |*| A) -⚬ A): (Done |*| LList1[A]) -⚬ LList1[A] =
      transform[A, Done, A](await)

    def eachAwait[A](using A: Junction.Positive[A]): (Done |*| LList1[A]) -⚬ LList1[A] =
      eachAwaitBy(A.awaitPosFst)
  }

  /** An endless source of elements, where the consumer decides whether to pull one more element or close.
    * Dual to [[LList]], in which the producer decides how many elements will be produced.
    */
  opaque type Endless[A] = Rec[[X] =>> One |&| (A |*| X)]
  object Endless {
    private def pack[A]: (One |&| (A |*| Endless[A])) -⚬ Endless[A] =
      dsl.pack[[X] =>> One |&| (A |*| X)]

    private def unpack[A]: Endless[A] -⚬ (One |&| (A |*| Endless[A])) =
      dsl.unpack

    def fromChoice[A]: (One |&| (A |*| Endless[A])) -⚬ Endless[A] =
      pack

    def toChoice[A]: Endless[A] -⚬ (One |&| (A |*| Endless[A])) =
      dsl.unpack

    def close[A]: Endless[A] -⚬ One =
      unpack > chooseL

    def pull[A]: Endless[A] -⚬ (A |*| Endless[A]) =
      unpack > chooseR

    def pullOnPing[A]: (Ping |*| Endless[A]) -⚬ (A |*| Endless[A]) =
      snd(unpack) > delayChoiceUntilPing > chooseR

    def create[X, A](
      onClose: X -⚬ One,
      onPull: X -⚬ (A |*| Endless[A]),
    ): X -⚬ Endless[A] =
      choice(onClose, onPull) > pack[A]

    def createWith[X, A, Y](
      onClose: X -⚬ Y,
      onPull: X -⚬ ((A |*| Endless[A]) |*| Y),
    ): X -⚬ (Endless[A] |*| Y) =
      choice(onClose > introFst, onPull) > coDistributeR > par(pack, id)

    def fromUnlimited[A]: Unlimited[A] -⚬ Endless[A] = rec { self =>
      create(
        onClose = Unlimited.discard,
        onPull  = Unlimited.getSome > snd(self)
      )
    }

    def unfold[S, A](f: S -⚬ (A |*| S)): S -⚬ (Endless[A] |*| S) = rec { self =>
      createWith[S, A, S](
        onClose = id[S],
        onPull = f > par(id, self) > assocRL,
      )
    }

    /** Signals when the consumer makes a choice, i.e. [[close]] or [[pull]]. */
    given [A]: Signaling.Negative[Endless[A]] =
      Signaling.Negative.from(par(id, unpack) > notifyChoice > pack)

    def split[A]: Endless[A] -⚬ (Endless[A] |*| Endless[A]) = rec { self =>
      val onFstAction: Endless[A] -⚬ (Endless[A] |*| Endless[A]) = {
        val onClose: Endless[A] -⚬ (One |*| Endless[A]) =
          introFst
        val onPull: Endless[A] -⚬ ((A |*| Endless[A]) |*| Endless[A]) =
          pull > par(id, self) > assocRL

        id                                    [                    Endless[A]                 |*| Endless[A]  ]
          ./<.fst(pack)                  .from[ (One                 |&|  (A |*| Endless[A])) |*| Endless[A]  ]
          ./<(coDistributeR)             .from[ (One |*| Endless[A]) |&| ((A |*| Endless[A])  |*| Endless[A]) ]
          ./<(choice(onClose, onPull))   .from[                   Endless[A]                                  ]
      }

      val onSndAction: Endless[A] -⚬ (Endless[A] |*| Endless[A]) =
        onFstAction > swap

      select(
        caseFstWins = onFstAction,
        caseSndWins = onSndAction,
      )
    }

    given [A]: Comonoid[Endless[A]] with {
      override def counit: Endless[A] -⚬ One                         = Endless.close
      override def split : Endless[A] -⚬ (Endless[A] |*| Endless[A]) = Endless.split
    }

    def toUnlimited[A]: Endless[A] -⚬ Unlimited[A] = rec { self =>
      Unlimited.create(
        case0 = close,
        case1 = pull > elimSnd(close),
        caseN = split > par(self, self),
      )
    }

    /** Pulls the given amount of elements and returns them in a list.
      *
      * **Note:** This method assembles a program whose size is proportional to _n_.
      */
    def take[A](n: Int): Endless[A] -⚬ LList[A] = {
      require(n >= 0, s"n must be non-negative, got $n")

      if (n > 0)
        pull > par(id, take(n - 1)) > LList.cons
      else
        close > LList.nil[A]
    }

    def map[A, B](f: A -⚬ B): Endless[A] -⚬ Endless[B] = rec { self =>
      create(
        onClose = close,
        onPull  = pull > par(f, self),
      )
    }

    def delayUntilPing[A]: (Ping |*| Endless[A]) -⚬ Endless[A] =
      snd(unpack) > delayChoiceUntilPing > pack

    def delayUntilPong[A]: Endless[A] -⚬ (Pong |*| Endless[A]) =
      unpack > delayChoiceUntilPong > snd(pack)

    /** Delays each next pull until the previously emitted element signalled. */
    def sequence[A](using A: Signaling.Positive[A]): Endless[A] -⚬ Endless[A] =
      mapSequentially(id)

    /** Delays each next pull until the [[Ping]] produced from the previous element. */
    def mapSequence[A, B](f: A -⚬ (Ping |*| B)): Endless[A] -⚬ Endless[B] =
      rec { self =>
        Endless.create(
          onClose = close[A],
          onPull  = λ { as =>
            val h  |*| t  = pull(as)
            val pi |*| b  = f(h)
            val po |*| t1 = delayUntilPong(t)
            returning(
              b |*| self(t1),
              rInvertPingPong(pi |*| po),
            )
          }
        )
      }

    def mapSequentially[A, B](f: A -⚬ B)(using Signaling.Positive[B]): Endless[A] -⚬ Endless[B] =
      mapSequence(f > notifyPosFst)

    def foldLeftSequentially[B, A](f: (B |*| A) -⚬ B)(using
      Signaling.Positive[B]
    ): (B |*| Endless[A]) -⚬ B =
      rec { self =>
        λ { case b |*| as =>
          val p |*| b1 = b :>> notifyPosFst
          switch ( injectLOnPing[Endless[A], One](p |*| as) )
            .is { case InL(as) =>
              val h |*| t = pull(as)
              self(f(b1 |*| h) |*| t)
            }
            .is { case InR(?(_)) => b1 }
            .end
        }
      }

    def foldMapSequentially[A, B](f: A -⚬ B)(using
      Signaling.Positive[B],
      Semigroup[B],
    ): Endless[A] -⚬ B = {
      val g: (B |*| A) -⚬ B =
        snd(f) > summon[Semigroup[B]].combine

      pull > fst(f) > foldLeftSequentially[B, A](g)
    }

    def pullN[A](n: Int): Endless[A] -⚬ (LList1[A] |*| Endless[A]) = {
      require(n > 0, s"n must be positive")

      pull > λ { case h |*| t =>
        if (n == 1)
          LList1.singleton(h) |*| t
        else
          val as |*| t1 = pullN(n-1)(t)
          LList1.cons1(h |*| as) |*| t1
      }
    }

    def unpull[A](using A: Affine[A]): (A |*| Endless[A]) -⚬ Endless[A] =
      create(
        onClose = λ { case ?(_) |*| as => close(as) },
        onPull  = id,
      )

    def groups[A](groupSize: Int): Endless[A] -⚬ Endless[LList1[A]] = rec { self =>
      require(groupSize > 0, s"group size must be positive")

      create(
        onClose = close,
        onPull  = pullN(groupSize) > snd(self),
      )
    }

    def groupMap[A, B](groupSize: Int, f: LList1[A] -⚬ B): Endless[A] -⚬ Endless[B] =
      groups(groupSize) > map(f)

    def mergePreferred[A](using
      A: Signaling.Positive[A],
      aff: Affine[A],
    ): (Endless[A] |*| Endless[A]) -⚬ Endless[A] = {
      def go: ((A |*| Endless[A]) |*| Endless[A]) -⚬ Endless[A] = rec { self =>
        λ { case (a |*| as) |*| bs =>
          val po |*| pi = constant(lInvertPongPing)
          val res: $[One |&| (A |*| Endless[A])] =
            switch ( race[Ping, A](pi |*| a) )
              .is { case InL(?(_) |*| a) =>
                (a |*| as |*| bs) :>> choice(
                  λ { case ?(_) |*| as |*| bs => close(as) alsoElim close(bs) },
                  λ { case   a  |*| as |*| bs =>
                    val b |*| bs1 = pull(bs)
                    switch ( race[A, A](a |*| b) )
                      .is { case InL(a |*| b)  => a |*| self(pull(as) |*| unpull[A](b |*| bs1)) }
                      .is { case InR(a |*| b) => b |*| self((a |*| as) |*| bs1) }
                      .end
                  },
                )
              }
              .is { case InR(?(_) |*| a) =>
                (a |*| as |*| bs) :>> choice(
                  λ { case ?(_) |*| as |*| bs => close(as) alsoElim close(bs) },
                  λ { case   a  |*| as |*| bs => a |*| self(pull(as) |*| bs) },
                )
              }
              .end
          (po |*| res) :>> notifyChoice :>> pack
        }
      }

      fst(pull) > go
    }

    def mergeEitherPreferred[A, B](using
      A: Signaling.Positive[A],
      B: Signaling.Positive[B],
      affA: Affine[A],
      affB: Affine[B],
    ): (Endless[A] |*| Endless[B]) -⚬ Endless[A |+| B] = {
      given Signaling.Positive[A |+| B] = Signaling.Positive.either(A, B)
      par(Endless.map(injectL), Endless.map(injectR)) > mergePreferred[A |+| B]
    }

    def poolBy[A: Signaling.Positive, Ā](
      lInvert: One -⚬ (Ā |*| A),
    ): LList1[A] -⚬ (Endless[A |*| Ā] |*| LList1[A]) =
      unfold(LList1.borrow(lInvert))

    def pool[A](using Signaling.Positive[A]): LList1[A] -⚬ (Endless[A |*| -[A]] |*| LList1[A]) =
      poolBy[A, -[A]](forevert[A])

    def poolReset[A, B](reset: B -⚬ A)(using
      Signaling.Positive[A]
    ): LList1[A] -⚬ (Endless[A |*| -[B]] |*| LList1[A]) =
      poolBy[A, -[B]](forevert[B] > snd(reset))
  }

  def listEndlessDuality[A, Ā](ev: Dual[A, Ā]): Dual[LList[A], Endless[Ā]] =
    new Dual[LList[A], Endless[Ā]] {
      override val rInvert: (LList[A] |*| Endless[Ā]) -⚬ One =
        λ.rec { self =>
          { case as |*| ns =>
            switch( as )
              .is { case LList.Nil(?(_)) => Endless.close(ns) }
              .is { case LList.Cons(a |*| as1) =>
                val n |*| ns1 = Endless.pull(ns)
                returning(self(as1 |*| ns1), ev.rInvert(a |*| n))
              }
              .end
          }
      }

      override val lInvert: One -⚬ (Endless[Ā] |*| LList[A]) = rec { self =>
        Endless.createWith(
          onClose = LList.nil[A],
          onPull  = self > introFst(ev.lInvert) > IXI > snd(LList.cons),
        )
      }
    }

  opaque type Lease = Done |*| Need
  object Lease {
    /** The [[Done]] signal on the outport signals when the lease is released. */
    def create: Done -⚬ (Lease |*| Done) =
      introSnd(lInvertSignal) > assocRL

    def release: Lease -⚬ One =
      rInvertSignal

    def releaseBy: (Done |*| Lease) -⚬ One =
      assocRL > fst(join) > rInvertSignal

    def notifyAcquired: Lease -⚬ (Ping |*| Lease) =
      fst(notifyDoneL) > assocLR

    def deferAcquisition: (Done |*| Lease) -⚬ Lease =
      assocRL > fst(join)

    def deferRelease: (Done |*| Lease) -⚬ Lease =
      λ { case (d |*| (leaseD |*| leaseN)) =>
        val (n1 |*| n2) = joinNeed(leaseN)
        (leaseD |*| n2) alsoElim rInvertSignal(d |*| n1)
      }
  }

  opaque type LeasePool =
    Unlimited[Lease] |*| Done

  object LeasePool {
    def fromList: LList1[Done] -⚬ LeasePool =
      Unlimited.poolBy[Done, Need](lInvertSignal) > snd(LList1.fold[Done])

    def allocate(n: Int): Done -⚬ LeasePool =
      LList1.fill(n)(id[Done]) > fromList

    /** Creates a pool from `S` with as many leases as are unfolded from `S` via `f`. */
    def createUnfold[S](f: S -⚬ (Done |*| Maybe[S])): S -⚬ LeasePool =
      LList1.unfold(f) > fromList

    def acquireLease: LeasePool -⚬ (Lease |*| LeasePool) =
      fst(Unlimited.getSome) > assocLR

    def close: LeasePool -⚬ Done =
      elimFst(Unlimited.discard)
  }

  /** Represents an acquired "token".
    * @tparam X how the interaction continues after returning the acquired token
    */
  private type Acquired[X] =
    // the acquired token
    Done |*|
    // continuation after returning the token
    Detained[X]

  private type LockF[X] =
      // result of the close action
      ( Done |&|
      // result of the acquire action
      ( Acquired[X] |&|
      // result of the tryAcquire action
      ( Acquired[X] |+| X
      )))

  opaque type Lock =
    Rec[LockF]

  opaque type AcquiredLock =
    Acquired[Lock]

  object Lock {
    def acquire: Lock -⚬ AcquiredLock =
      unpack[LockF] > chooseR > chooseL

    def tryAcquire: Lock -⚬ (AcquiredLock |+| Lock) =
      unpack[LockF] > chooseR > chooseR

    def close: Lock -⚬ Done =
      unpack[LockF] > chooseL

    def newLock: Done -⚬ Lock =
      rec { newLock =>
        choice(
          id[Done],
          choice(
            introSnd(Detained.thunk(newLock)),
            introSnd(Detained.thunk(newLock)) > injectL,
          ),
        ) > pack[LockF]
      }

    def share: Lock -⚬ (Lock |*| Lock) =
      rec { share =>
        val branchByFst: Lock -⚬ (Lock |*| Lock) = {

          val caseClose: Lock -⚬ (Done |*| Lock) =
            introFst(done)

          val acquiredByFst: AcquiredLock -⚬ (AcquiredLock |*| Lock) = rec { acquiredByFst =>
            val go: Detained[Lock] -⚬ (Detained[Lock] |*| Lock) = rec { go =>
              // when the acquired lock is released before action is taken on the other lock handle
              val expectRelease: Detained[Lock] -⚬ (Detained[Lock] |*| Lock) =
                Detained(Detained.releaseBy > share) > Transportive[Detained].outR

              // when action is taken on the other lock handle while lock is acquired by the first handle
              val branchBySnd: Detained[Lock] -⚬ (Detained[Lock] |*| Lock) = {
                val caseClose: Detained[Lock] -⚬ (Detained[Lock] |*| Done) =
                    introSnd(done)

                val caseAcquire: Detained[Lock] -⚬ (Detained[Lock] |*| AcquiredLock) =
                    // release and re-acquire, to give chance to others
                    Detained(Detained.releaseBy > Lock.acquire > acquiredByFst > swap) > Transportive[Detained].outR

                val caseTryAcquire: Detained[Lock] -⚬ (Detained[Lock] |*| (AcquiredLock |+| Lock)) =
                    go > snd(injectR)

                choice(
                  caseClose,
                  choice(
                    caseAcquire,
                    caseTryAcquire,
                  ) > coDistributeL
                ) > coDistributeL > snd(pack[LockF])
              }

              choice(expectRelease, branchBySnd) > selectBy(Detained.notifyReleaseNeg, notifyAction)
            }

            snd(go) > assocRL
          }

          val caseAcquire: Lock -⚬ (AcquiredLock |*| Lock) =
            Lock.acquire > acquiredByFst

          val caseTryAcquire: Lock -⚬ ((AcquiredLock |+| Lock) |*| Lock) =
            Lock.tryAcquire > either(
              acquiredByFst > fst(injectL),
              share > fst(injectR),
            )

          choice(
            caseClose,
            choice(
              caseAcquire,
              caseTryAcquire,
            ) > coDistributeR,
          ) > coDistributeR > fst(pack[LockF])
        }

        val branchBySnd: Lock -⚬ (Lock |*| Lock) =
          branchByFst > swap

        choice(branchByFst, branchBySnd) > selectBy(notifyAction, notifyAction)
      }

    private def notifyAction: (Pong |*| Lock) -⚬ Lock =
      snd(unpack[LockF]) > notifyChoiceAndRight(notifyChoice) > pack[LockF]

    given CloseableCosemigroup[Lock] =
      new CloseableCosemigroup[Lock] {
        override def split: Lock -⚬ (Lock |*| Lock) =
          Lock.share

        override def close: Lock -⚬ Done =
          Lock.close
      }
  }

  object AcquiredLock {
    def release: AcquiredLock -⚬ Lock =
      Detained.releaseBy

    /** Acquisition will not be complete until also the given [[Done]] signal arrives. */
    def detainAcquisition: (Done |*| AcquiredLock) -⚬ AcquiredLock =
      assocRL > fst(join)

    /** Acquisition will not be complete until also the given [[Ping]] signal arrives. */
    def deferAcquisition: (Ping |*| AcquiredLock) -⚬ AcquiredLock =
      fst(strengthenPing) > detainAcquisition

    /** Notifies when the lock is acquired. */
    def notifyAcquisition: AcquiredLock -⚬ (Ping |*| AcquiredLock) =
      fst(notifyDoneL) > assocLR

    /** Subsequent [[release]] won't have effect until also the given [[Done]] signal arrives. */
    def detainRelease: (Done |*| AcquiredLock) -⚬ AcquiredLock =
      XI > snd(Detained.extendDetentionUntil)

    /** Subsequent [[release]] won't have effect until also the given [[Ping]] signal arrives. */
    def deferRelease: (Ping |*| AcquiredLock) -⚬ AcquiredLock =
      fst(strengthenPing) > detainRelease

    given acquisition: SignalingJunction.Positive[AcquiredLock] =
      new SignalingJunction.Positive[AcquiredLock] {
        override def notifyPosFst: AcquiredLock -⚬ (Ping |*| AcquiredLock) =
          notifyAcquisition

        override def awaitPosFst: (Done |*| AcquiredLock) -⚬ AcquiredLock =
          detainAcquisition
      }
  }

  extension (acquiredLock: $[AcquiredLock])(using LambdaContext) {
    infix def deferReleaseUntil(ping: $[Ping]): $[AcquiredLock] =
      AcquiredLock.deferRelease(ping |*| acquiredLock)

    infix def detainReleaseUntil(done: $[Done]): $[AcquiredLock] =
      AcquiredLock.detainRelease(done |*| acquiredLock)
  }

  /** Function object (internal hom) is contravariant in the input type. */
  def input[C]: ContraFunctor[[x] =>> x =⚬ C] =
    new ContraFunctor[[x] =>> x =⚬ C] {
      override val category =
        dsl.category

      override def lift[A, B](f: A -⚬ B): (B =⚬ C) -⚬ (A =⚬ C) =
        id                         [ (B =⚬ C) |*| A ]
          ./>.snd(f)            .to[ (B =⚬ C) |*| B ]
          ./>(eval)             .to[       C        ]
          .as[ ((B =⚬ C) |*| A)  -⚬        C        ]
          .curry
    }

  /** Function object (internal hom) is covariant in the output type. */
  def output[A]: Functor[[x] =>> A =⚬ x] =
    new Functor[[x] =>> A =⚬ x] {
      override val category =
        dsl.category

      override def lift[B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
        out(f)
    }

  extension [A, B](f: A -⚬ B) {
    def curry[A1, A2](using ev: A =:= (A1 |*| A2)): A1 -⚬ (A2 =⚬ B) =
      dsl.curry(ev.substituteCo[λ[x => x -⚬ B]](f))

    def uncurry[B1, B2](using ev: B =:= (B1 =⚬ B2)): (A |*| B1) -⚬ B2 =
      dsl.uncurry(ev.substituteCo(f))
  }

  extension [F[_], A, B](f: FocusedCo[F, A =⚬ B]) {
    def input: FocusedContra[λ[x => F[x =⚬ B]], A] =
      f.zoomContra(lib.input[B])

    def output: FocusedCo[λ[x => F[A =⚬ x]], B] =
      f.zoomCo(lib.output[A])
  }

  extension [F[_], A, B](f: FocusedContra[F, A =⚬ B]) {
    def input: FocusedCo[λ[x => F[x =⚬ B]], A] =
      f.zoomContra(lib.input[B])

    def output: FocusedContra[λ[x => F[A =⚬ x]], B] =
      f.zoomCo(lib.output[A])
  }

  def zapPremises[A, Ā, B, C](using ev: Dual[A, Ā]): ((A =⚬ B) |*| (Ā =⚬ C)) -⚬ (B |*| C) = {
    id                              [  (A =⚬ B) |*| (Ā =⚬ C)                ]
      ./>(introSnd(ev.lInvert))  .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (Ā |*| A) ]
      ./>.snd(swap)              .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (A |*| Ā) ]
      ./>(IXI)                   .to[ ((A =⚬ B) |*| A) |*| ((Ā =⚬ C) |*| Ā) ]
      ./>(par(eval, eval))       .to[        B         |*|        C         ]
  }

  /** Given `A` and `B` concurrently (`A |*| B`), we can suggest that `A` be consumed before `B`
    * by turning it into `Ā =⚬ B`, where `Ā` is the dual of `A`.
    */
  def unveilSequentially[A, Ā, B](using ev: Dual[A, Ā]): (A |*| B) -⚬ (Ā =⚬ B) =
    id[(A |*| B) |*| Ā]           .to[ (A |*|  B) |*| Ā  ]
      ./>(assocLR)                .to[  A |*| (B  |*| Ā) ]
      ./>.snd(swap)               .to[  A |*| (Ā  |*| B) ]
      ./>(assocRL)                .to[ (A |*|  Ā) |*| B  ]
      ./>(elimFst(ev.rInvert))    .to[                B  ]
      .as[ ((A |*| B) |*| Ā) -⚬ B ]
      .curry

  /** Make a function `A =⚬ B` ''"absorb"'' a `C` and return it as part of its output, i.e. `A =⚬ (B |*| C)`. */
  def absorbR[A, B, C]: ((A =⚬ B) |*| C) -⚬ (A =⚬ (B |*| C)) =
    id[((A =⚬ B) |*| C) |*| A]  .to[ ((A =⚬ B) |*| C) |*| A ]
      ./>(assocLR)              .to[ (A =⚬ B) |*| (C |*| A) ]
      ./>.snd(swap)             .to[ (A =⚬ B) |*| (A |*| C) ]
      ./>(assocRL)              .to[ ((A =⚬ B) |*| A) |*| C ]
      ./>.fst(eval)             .to[        B         |*| C ]
      .as[ (((A =⚬ B) |*| C) |*| A) -⚬ (B |*| C) ]
      .curry

  def inversionDuality[A]: Dual[A, -[A]] =
    new Dual[A, -[A]] {
      override val rInvert: (A |*| -[A]) -⚬ One = backvert[A]
      override val lInvert: One -⚬ (-[A] |*| A) = forevert[A]
    }

  given ContraFunctor[-] with {
    override val category =
      dsl.category

    override def lift[A, B](f: A -⚬ B): -[B] -⚬ -[A] =
      contrapositive(f)
  }
}
