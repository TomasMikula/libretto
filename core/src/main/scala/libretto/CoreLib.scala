package libretto

import libretto.unapply._
import scala.annotation.tailrec

object CoreLib {
  def apply(dsl: CoreDSL): CoreLib[dsl.type] =
    new CoreLib(dsl)
}

class CoreLib[DSL <: CoreDSL](val dsl: DSL) { lib =>
  import dsl._

  def fst[A, B, C](f: A -⚬ B): (A |*| C) -⚬ (B |*| C) =
    par(f, id[C])

  def snd[A, B, C](f: B -⚬ C): (A |*| B) -⚬ (A |*| C) =
    par(id[A], f)

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
          .introSnd(lInvert)    .to[ A |*| (B |*| A) ]
          .assocRL              .to[ (A |*| B) |*| A ]
          .elimFst(rInvert)     .to[               A ],
        id[A]
      )

    /** Law stating that [[lInvert]] followed by [[rInvert]] is identity. */
    def law_lr_id: Equal[B -⚬ B] =
      Equal(
        id[B]                   .to[               B ]
          .introFst(lInvert)    .to[ (B |*| A) |*| B ]
          .assocLR              .to[ B |*| (A |*| B) ]
          .elimSnd(rInvert)     .to[ B               ],
        id[B]
      )
  }

  object Dual {
    /** Convenience method to summon implicit instances of [[dsl.Dual]]. */
    def apply[A, B](implicit ev: Dual[A, B]): Dual[A, B] = ev
  }

  def rInvert[A, B](implicit ev: Dual[A, B]): (A |*| B) -⚬ One =
    ev.rInvert

  def lInvert[A, B](implicit ev: Dual[A, B]): One -⚬ (B |*| A) =
    ev.lInvert

  /** Witnesses that `F` is a covariant endofunctor on the category `-⚬`. */
  trait Functor[F[_]] { self =>
    def lift[A, B](f: A -⚬ B): F[A] -⚬ F[B]

    /** Composition with another covariant functor. */
    def ∘[G[_]](that: Functor[G]): Functor[λ[x => F[G[x]]]] = new Functor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[A]] -⚬ F[G[B]] = self.lift(that.lift(f))
    }

    /** Composition with a contravariant functor. Results in a contravariant functor. */
    def ∘[G[_]](that: ContraFunctor[G]): ContraFunctor[λ[x => F[G[x]]]] = new ContraFunctor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[B]] -⚬ F[G[A]] = self.lift(that.lift(f))
    }
  }

  /** Witnesses that `F` is a contravariant endofunctor on the category `-⚬`. */
  trait ContraFunctor[F[_]] { self =>
    def lift[A, B](f: A -⚬ B): F[B] -⚬ F[A]

    /** Composition with a covariant functor. Results in a contravariant functor. */
    def ∘[G[_]](that: Functor[G]): ContraFunctor[λ[x => F[G[x]]]] = new ContraFunctor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[B]] -⚬ F[G[A]] = self.lift(that.lift(f))
    }

    /** Composition with another contravariant functor. Results in a covariant functor. */
    def ∘[G[_]](that: ContraFunctor[G]): Functor[λ[x => F[G[x]]]] = new Functor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[A]] -⚬ F[G[B]] = self.lift(that.lift(f))
    }
  }

  /** Witnesses that `F` is a bifunctor (covariant in both variables). */
  trait Bifunctor[F[_, _]] {
    def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): F[A, C] -⚬ F[B, D]

    def fst[B]: Functor[F[*, B]] = new Functor[F[*, B]] {
      def lift[A1, A2](f: A1 -⚬ A2): F[A1, B] -⚬ F[A2, B] =
        Bifunctor.this.lift[A1, A2, B, B](f, id[B])
    }

    def snd[A]: Functor[F[A, *]] = new Functor[F[A, *]] {
      def lift[B1, B2](g: B1 -⚬ B2): F[A, B1] -⚬ F[A, B2] =
        Bifunctor.this.lift[A, A, B1, B2](id[A], g)
    }

    def inside[G[_]](implicit G: Functor[G]): Bifunctor[λ[(x, y) => G[F[x, y]]]] =
      new Bifunctor[λ[(x, y) => G[F[x, y]]]] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): G[F[A, C]] -⚬ G[F[B, D]] =
          G.lift(Bifunctor.this.lift(f, g))
      }
  }

  object Bifunctor {
    def apply[F[_, _]](implicit ev: Bifunctor[F]): Bifunctor[F] = ev
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
    implicit def outportInstance[A]: Externalizer[[x] =>> A -⚬ x] =
      new Externalizer[[x] =>> A -⚬ x] {
        def lift[B, C](f: B -⚬ C): (A -⚬ B) => (A -⚬ C) =
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
    implicit def inportInstance[C]: ContraExternalizer[[x] =>> x -⚬ C] =
      new ContraExternalizer[[x] =>> x -⚬ C] {
        def lift[A, B](f: A -⚬ B): (B -⚬ C) => (A -⚬ C) =
          f > _
      }
  }

  /** A type alias expressing the ''intent'' that `A` is delayed (in some sense) until a signal ([[Need]]) is received.
    * Equivalent to `Done =⚬ A`, but the formulation as `Need |*| A` does not rely on the more powerful concept
    * of ''function types'' (internal hom objects), i.e. does not require [[ClosedDSL]].
    */
  opaque type Delayed[A] = Need |*| A
  object Delayed {
    def apply[A](f: Done -⚬ A): One -⚬ Delayed[A] =
      lInvertSignal > par(id, f)

    def fst[A, B](f: Done -⚬ (A |*| B)): One -⚬ (Delayed[A] |*| B) =
      apply(f).assocRL

    def snd[A, B](f: Done -⚬ (A |*| B)): One -⚬ (A |*| Delayed[B]) =
      apply(f) > XI

    def from[A, B](f: (Done |*| A) -⚬ B): A -⚬ Delayed[B] =
      id[A] > introFst(lInvertSignal) > |*|.assocLR > par(id, f)

    def triggerBy[A]: (Done |*| Delayed[A]) -⚬ A =
      |*|.assocRL > elimFst(rInvertSignal)

    def force[A]: Delayed[A] -⚬ A =
      elimFst(need)

    /** Signals when it is triggered, awaiting delays the trigger. */
    implicit def signalingJunction[A]: SignalingJunction.Negative[Delayed[A]] =
      SignalingJunction.Negative.byFst
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

      def law_awaitIdentity: Equal[(One |*| A) -⚬ A] =
        Equal(
          par(done, id) > awaitPosFst,
          elimFst,
        )

      def law_AwaitComposition: Equal[(Done |*| (Done |*| A)) -⚬ A] =
        Equal(
          par(id, awaitPosFst) > awaitPosFst,
          |*|.assocRL > par(join, id) > awaitPosFst,
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

      def law_awaitIdentity: Equal[A -⚬ (One |*| A)] =
        Equal(
          awaitNegFst > par(need, id),
          introFst,
        )

      def law_awaitComposition: Equal[A -⚬ (Need |*| (Need |*| A))] =
        Equal(
          awaitNegFst > par(id, awaitNegFst),
          awaitNegFst > par(joinNeed, id) > |*|.assocLR,
        )
    }

    object Positive {
      def from[A](await: (Done |*| A) -⚬ A): Junction.Positive[A] =
        new Junction.Positive[A] {
          override def awaitPosFst: (Done |*| A) -⚬ A =
            await
        }

      implicit def junctionDone: Junction.Positive[Done] =
        from(join)

      def byFst[A, B](implicit A: Junction.Positive[A]): Junction.Positive[A |*| B] =
        from(|*|.assocRL.>.fst(A.awaitPosFst))

      def bySnd[A, B](implicit B: Junction.Positive[B]): Junction.Positive[A |*| B] =
        from(XI > par(id[A], B.awaitPosFst))

      def both[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |*| B] =
        from(par(fork, id) > IXI > par(A.awaitPosFst, B.awaitPosFst))

      def delegateToEither[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |+| B] =
        from( distributeL[Done, A, B].bimap(A.awaitPosFst, B.awaitPosFst) )

      def delayEither[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |+| B] =
        from( delayEitherUntilDone.bimap(A.awaitPosFst, B.awaitPosFst) )

      def delegateToChosen[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |&| B] =
        from( coFactorL[Done, A, B].bimap(A.awaitPosFst, B.awaitPosFst) )

      def delayChoice[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |&| B] =
        from( delayChoiceUntilDone.bimap(A.awaitPosFst, B.awaitPosFst) )

      def rec[F[_]](implicit F: Junction.Positive[F[Rec[F]]]): Junction.Positive[Rec[F]] =
        from(par(id, unpack) > F.awaitPosFst > pack)

      def rec[F[_]](implicit F: ∀[λ[x => Junction.Positive[F[x]]]]): Junction.Positive[Rec[F]] =
        rec(F[Rec[F]])

      def rec[F[_]](f: Junction.Positive[Rec[F]] => Junction.Positive[F[Rec[F]]]): Junction.Positive[Rec[F]] =
        from(dsl.rec(g => par(id, unpack) > f(from(g)).awaitPosFst > pack))
    }

    object Negative {
      def from[A](await: A -⚬ (Need |*| A)): Junction.Negative[A] =
        new Junction.Negative[A] {
          override def awaitNegFst: A -⚬ (Need |*| A) =
            await
        }

      implicit def junctionNeed: Junction.Negative[Need] =
        from(joinNeed)

      def byFst[A, B](implicit A: Junction.Negative[A]): Junction.Negative[A |*| B] =
        from(par(A.awaitNegFst, id[B]).assocLR)

      def bySnd[A, B](implicit B: Junction.Negative[B]): Junction.Negative[A |*| B] =
        from(par(id[A], B.awaitNegFst) > XI)

      def both[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |*| B] =
        from(par(A.awaitNegFst, B.awaitNegFst) > IXI > par(forkNeed, id))

      def delegateToEither[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        from( id[A |+| B].bimap(A.awaitNegFst, B.awaitNegFst).factorL )

      def delayEither[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        from( id[A |+| B].bimap(A.awaitNegFst, B.awaitNegFst) > delayEitherUntilNeed )

      def delegateToChosen[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        from( id[A |&| B].bimap(A.awaitNegFst, B.awaitNegFst).coDistributeL )

      def delayChoice[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        from( id[A |&| B].bimap(A.awaitNegFst, B.awaitNegFst) > delayChoiceUntilNeed )

      def rec[F[_]](implicit F: Junction.Negative[F[Rec[F]]]): Junction.Negative[Rec[F]] =
        from(unpack[F] > F.awaitNegFst > par(id, pack[F]))

      def rec[F[_]](implicit F: ∀[λ[x => Junction.Negative[F[x]]]]): Junction.Negative[Rec[F]] =
        rec(F[Rec[F]])

      def rec[F[_]](f: Junction.Negative[Rec[F]] => Junction.Negative[F[Rec[F]]]): Junction.Negative[Rec[F]] =
        from(dsl.rec(g => unpack > f(from(g)).awaitNegFst > par(id, pack)))
    }

    /** [[Positive]] junction can be made to await a negative (i.e. [[Need]]) signal,
      * by inverting the signal ([[lInvertSignal]]) and awaiting the inverted positive signal.
      */
    def invert[A](A: Positive[A]): Negative[A] =
      new Negative[A] {
        override def awaitNegFst: A -⚬ (Need |*| A) =
          id                                 [                      A  ]
            .introFst(lInvertSignal)      .to[ (Need |*|  Done) |*| A  ]
            .assocLR                      .to[  Need |*| (Done  |*| A) ]
            .>.snd(A.awaitPosFst)         .to[  Need |*|            A  ]
      }

    /** [[Negative]] junction can be made to await a positive (i.e. [[Done]]) signal,
      * by inverting the signal ([[rInvertSignal]]) and awaiting the inverted negative signal.
      */
    def invert[A](A: Negative[A]): Positive[A] =
      new Positive[A] {
        override def awaitPosFst: (Done |*| A) -⚬ A =
          id                                 [  Done |*|            A  ]
            .>.snd(A.awaitNegFst)         .to[  Done |*| (Need  |*| A) ]
            .assocRL                      .to[ (Done |*|  Need) |*| A  ]
            .elimFst(rInvertSignal)       .to[                      A  ]
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

      def law_signalIdentity: Equal[A -⚬ (RTerminus |*| A)] =
        Equal(
          signalPosFst > par(delayIndefinitely, id),
          id[A] > introFst(done > delayIndefinitely),
        )

      def law_awaitComposition: Equal[A -⚬ (Done |*| (Done |*| A))] =
        Equal(
          signalPosFst > par(id, signalPosFst),
          signalPosFst > par(fork, id) > |*|.assocLR,
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
          |*|.assocRL > par(forkNeed, id) > signalNegFst,
        )
    }

    object Positive {
      def from[A](notifyFst: A -⚬ (Ping |*| A)): Signaling.Positive[A] =
        new Signaling.Positive[A] {
          override def notifyPosFst: A -⚬ (Ping |*| A) =
            notifyFst
        }

      implicit def signalingDone: Signaling.Positive[Done] =
        from(notifyDoneL)

      def byFst[A, B](implicit A: Signaling.Positive[A]): Signaling.Positive[A |*| B] =
        from(par(A.notifyPosFst, id[B]).assocLR)

      def bySnd[A, B](implicit B: Signaling.Positive[B]): Signaling.Positive[A |*| B] =
        from(par(id[A], B.notifyPosFst) > XI)

      def both[A, B](implicit A: Signaling.Positive[A], B: Signaling.Positive[B]): Signaling.Positive[A |*| B] =
        from(par(A.notifyPosFst, B.notifyPosFst) > IXI > par(joinPing, id))

      /** Signals when it is decided which side of the [[|+|]] is present. */
      implicit def either[A, B]: Signaling.Positive[A |+| B] =
        from(dsl.notifyEither[A, B])

      def rec[F[_]](implicit F: Positive[F[Rec[F]]]): Positive[Rec[F]] =
        from(unpack > F.notifyPosFst > par(id, pack))

      def rec[F[_]](implicit F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        rec(F[Rec[F]])

      def rec[F[_]](f: Positive[Rec[F]] => Positive[F[Rec[F]]]): Positive[Rec[F]] =
        from(dsl.rec(g => unpack > f(from(g)).notifyPosFst > par(id, pack)))
    }

    object Negative {
      def from[A](notifyFst: (Pong |*| A) -⚬ A): Signaling.Negative[A] =
        new Signaling.Negative[A] {
          override def notifyNegFst: (Pong |*| A) -⚬ A =
            notifyFst
        }

      implicit def signalingNeed: Signaling.Negative[Need] =
        from(notifyNeedL)

      def byFst[A, B](implicit A: Signaling.Negative[A]): Signaling.Negative[A |*| B] =
        from(|*|.assocRL.>.fst(A.notifyNegFst))

      def bySnd[A, B](implicit B: Signaling.Negative[B]): Signaling.Negative[A |*| B] =
        from(XI > par(id[A], B.notifyNegFst))

      def both[A, B](implicit A: Signaling.Negative[A], B: Signaling.Negative[B]): Signaling.Negative[A |*| B] =
        from(par(joinPong, id) > IXI > par(A.notifyNegFst, B.notifyNegFst))

      /** Signals when the choice is made between [[A]] and [[B]]. */
      implicit def choice[A, B]: Signaling.Negative[A |&| B] =
        from(dsl.notifyChoice[A, B])

      def rec[F[_]](implicit F: Negative[F[Rec[F]]]): Negative[Rec[F]] =
        from(par(id, unpack) > F.notifyNegFst > pack)

      def rec[F[_]](implicit F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        rec(F[Rec[F]])

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
            .>.snd(A.notifyPosFst)                .to[  Pong |*| (Ping  |*| A) ]
            .assocRL                              .to[ (Pong |*|  Ping) |*| A  ]
            .elimFst(swap > rInvertPingPong)      .to[                      A  ]
      }

    /** [[Signaling.Negative]] can be made to produce a positive (i.e. [[Done]]) signal,
      * by inverting the produced signal (via [[lInvertSignal]]).
      */
    def invert[A](A: Negative[A]): Positive[A] =
      new Positive[A] {
        override def notifyPosFst: A -⚬ (Ping |*| A) =
          id                                         [                      A  ]
            .introFst(lInvertPongPing > swap)     .to[ (Ping |*|  Pong) |*| A  ]
            .assocLR                              .to[  Ping |*| (Pong  |*| A) ]
            .>.snd(A.notifyNegFst)                .to[  Ping |*|            A  ]
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
          par(fork, id) > |*|.assocLR > par(id, awaitPos > signalPos) > |*|.assocRL > par(join, id),
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
          par(joinNeed, id) > |*|.assocLR > par(id, signalNeg > awaitNeg) > |*|.assocRL > par(forkNeed, id),
        )
    }

    object Positive {
      def from[A](s: Signaling.Positive[A], j: Junction.Positive[A]): SignalingJunction.Positive[A] =
        new SignalingJunction.Positive[A] {
          override def notifyPosFst: A -⚬ (Ping |*| A) = s.notifyPosFst
          override def awaitPosFst: (Done |*| A) -⚬ A = j.awaitPosFst
        }

      implicit def signalingJunctionPositiveDone: SignalingJunction.Positive[Done] =
        Positive.from(
          Signaling.Positive.signalingDone,
          Junction.Positive.junctionDone,
        )

      def byFst[A, B](implicit A: Positive[A]): Positive[A |*| B] =
        Positive.from(
          Signaling.Positive.byFst[A, B],
          Junction.Positive.byFst[A, B],
        )

      def bySnd[A, B](implicit B: Positive[B]): Positive[A |*| B] =
        Positive.from(
          Signaling.Positive.bySnd[A, B],
          Junction.Positive.bySnd[A, B],
        )

      def both[A, B](implicit A: Positive[A], B: Positive[B]): Positive[A |*| B] =
        Positive.from(
          Signaling.Positive.both[A, B],
          Junction.Positive.both[A, B],
        )

      /** Signals when the `|+|` is decided, awaiting delays (the publication of) the decision and thed is delegated
        * to the respective side.
        */
      def eitherPos[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Positive[A |+| B] =
        Positive.from(
          Signaling.Positive.either[A, B],
          Junction.Positive.delayEither[A, B],
        )

      /** Signals when the `|+|` is decided, awaiting delays (the publication of) the decision and then is delegated
        * to the respective side, which awaits an inversion of the original signal.
        */
      def eitherNeg[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Positive[A |+| B] =
        Positive.from(
          Signaling.Positive.either[A, B],
          Junction.Positive.delayEither(
            Junction.invert(A),
            Junction.invert(B),
          ),
        )

      def rec[F[_]](implicit F: Positive[F[Rec[F]]]): Positive[Rec[F]] =
        Positive.from(
          Signaling.Positive.rec(F),
          Junction.Positive.rec(F),
        )

      def rec[F[_]](implicit F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        rec(F[Rec[F]])

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

      implicit def signalingJunctionNegativeNeed: SignalingJunction.Negative[Need] =
        Negative.from(
          Signaling.Negative.signalingNeed,
          Junction.Negative.junctionNeed,
        )

      def byFst[A, B](implicit A: Negative[A]): Negative[A |*| B] =
        Negative.from(
          Signaling.Negative.byFst[A, B],
          Junction.Negative.byFst[A, B],
        )

      def bySnd[A, B](implicit B: Negative[B]): Negative[A |*| B] =
        Negative.from(
          Signaling.Negative.bySnd[A, B],
          Junction.Negative.bySnd[A, B],
        )

      def both[A, B](implicit A: Negative[A], B: Negative[B]): Negative[A |*| B] =
        Negative.from(
          Signaling.Negative.both[A, B],
          Junction.Negative.both[A, B],
        )

      /** Signals when the choice (`|&|`) is made, awaiting delays the choice and then is delegated to the chosen side. */
      def choiceNeg[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Negative[A |&| B] =
        Negative.from(
          Signaling.Negative.choice[A, B],
          Junction.Negative.delayChoice[A, B],
        )

      /** Signals when the choice (`|&|`) is made, awaiting delays the choice and then is delegated to the chosen side,
        * which awaits inversion of the original signal.
        */
      def choicePos[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Negative[A |&| B] =
        Negative.from(
          Signaling.Negative.choice[A, B],
          Junction.Negative.delayChoice(
            Junction.invert(A),
            Junction.invert(B),
          ),
        )

      def rec[F[_]](implicit F: Negative[F[Rec[F]]]): Negative[Rec[F]] =
        Negative.from(
          Signaling.Negative.rec(F),
          Junction.Negative.rec(F),
        )

      def rec[F[_]](implicit F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        rec(F[Rec[F]])

      def rec[F[_]](
        f: Signaling.Negative[Rec[F]] => Signaling.Negative[F[Rec[F]]],
        g: Junction.Negative[Rec[F]] => Junction.Negative[F[Rec[F]]],
      ): SignalingJunction.Negative[Rec[F]] =
        from(Signaling.Negative.rec(f), Junction.Negative.rec(g))
    }
  }

  def notifyPosFst[A](implicit A: Signaling.Positive[A]): A -⚬ (Ping |*| A) =
    A.notifyPosFst

  def notifyPosSnd[A](implicit A: Signaling.Positive[A]): A -⚬ (A |*| Ping) =
    A.notifyPosSnd

  def notifyNegFst[A](implicit A: Signaling.Negative[A]): (Pong |*| A) -⚬ A =
    A.notifyNegFst

  def notifyNegSnd[A](implicit A: Signaling.Negative[A]): (A |*| Pong) -⚬ A =
    A.notifyNegSnd

  def signalPosFst[A](implicit A: Signaling.Positive[A]): A -⚬ (Done |*| A) =
    A.signalPosFst

  def signalPosSnd[A](implicit A: Signaling.Positive[A]): A -⚬ (A |*| Done) =
    A.signalPosSnd

  def signalNegFst[A](implicit A: Signaling.Negative[A]): (Need |*| A) -⚬ A =
    A.signalNegFst

  def signalNegSnd[A](implicit A: Signaling.Negative[A]): (A |*| Need) -⚬ A =
    A.signalNegSnd

  def awaitPingFst[A](implicit A: Deferrable.Positive[A]): (Ping |*| A) -⚬ A =
    A.awaitPingFst

  def awaitPingSnd[A](implicit A: Deferrable.Positive[A]): (A |*| Ping) -⚬ A =
    A.awaitPingSnd

  def awaitPongFst[A](implicit A: Deferrable.Negative[A]): A -⚬ (Pong |*| A) =
    A.awaitPongFst

  def awaitPongSnd[A](implicit A: Deferrable.Negative[A]): A -⚬ (A |*| Pong) =
    A.awaitPongSnd

  def awaitPosFst[A](implicit A: Junction.Positive[A]): (Done |*| A) -⚬ A =
    A.awaitPosFst

  def awaitPosSnd[A](implicit A: Junction.Positive[A]): (A |*| Done) -⚬ A =
    A.awaitPosSnd

  def awaitNegFst[A](implicit A: Junction.Negative[A]): A -⚬ (Need |*| A) =
    A.awaitNegFst

  def awaitNegSnd[A](implicit A: Junction.Negative[A]): A -⚬ (A |*| Need) =
    A.awaitNegSnd

  def delayUsing[A](f: Done -⚬ Done)(implicit A: SignalingJunction.Positive[A]): A -⚬ A =
    A.delayUsing(f)

  def delayUsing[A](f: Need -⚬ Need)(implicit A: SignalingJunction.Negative[A]): A -⚬ A =
    A.delayUsing(f)

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
    id                                       [           Need  |*|           Need  ]
      .<(par(notifyNeedL, notifyNeedL)) .from[ (Pong |*| Need) |*| (Pong |*| Need) ]
      .<(IXI)                           .from[ (Pong |*| Pong) |*| (Need |*| Need) ]
      .<(par(selectPair, joinNeed))     .from[ ( One |&| One ) |*|      Need       ]
      .<(coDistributeR)                 .from[  (One |*| Need) |&| (One |*| Need)  ]
      .<(|&|.bimap(introFst, introFst)) .from[           Need  |&|          Need   ]

  def race[A, B](implicit
    A: Signaling.Positive[A],
    B: Signaling.Positive[B],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    id                                               [                  A  |*|           B         ]
      .>(par(A.notifyPosFst, B.notifyPosFst))     .to[        (Ping |*| A) |*| (Ping |*| B)        ]
      .>(IXI)                                     .to[        (Ping |*| Ping) |*| (A |*| B)        ]
      .>.fst(racePair)                            .to[        ( One |+| One ) |*| (A |*| B)        ]
      .>(distributeR)                             .to[ (One |*| (A |*| B)) |+| (One |*| (A |*| B)) ]
      .>(|+|.bimap(elimFst, elimFst))             .to[          (A |*| B)  |+|          (A |*| B)  ]

  def race[A: Signaling.Positive, B: Signaling.Positive, C](
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

  def raceAgainstL[A](implicit A: SignalingJunction.Positive[A]): (Done |*| A) -⚬ (A |+| A) =
    id                                               [  Done        |*|            A  ]
      .>.snd(A.signalPos).assocRL                 .to[ (Done        |*|  Done) |*| A  ]
      .>.fst(raceDone)                            .to[ (Done        |+|  Done) |*| A  ]
      .distributeR                                .to[ (Done |*| A) |+| (Done  |*| A) ]
      .bimap(A.awaitPos, A.awaitPos)              .to[           A  |+|            A  ]

  def raceAgainstR[A](implicit A: SignalingJunction.Positive[A]): (A |*| Done) -⚬ (A |+| A) =
    swap > raceAgainstL > |+|.swap

  def select[A, B](implicit
    A: Signaling.Negative[A],
    B: Signaling.Negative[B],
  ): ((A |*| B) |&| (A |*| B)) -⚬ (A |*| B) =
    id                                               [          (A |*| B)  |&|          (A |*| B)  ]
      .>(|&|.bimap(introFst, introFst))           .to[ (One |*| (A |*| B)) |&| (One |*| (A |*| B)) ]
      .>(coDistributeR)                           .to[        ( One |&| One ) |*| (A |*| B)        ]
      .>.fst(selectPair)                          .to[        (Pong |*| Pong) |*| (A |*| B)        ]
      .>(IXI)                                     .to[        (Pong |*| A) |*| (Pong |*| B)        ]
      .par(A.notifyNegFst, B.notifyNegFst)        .to[                  A  |*|           B         ]

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

  def selectAgainstL[A](implicit A: SignalingJunction.Negative[A]): (A |&| A) -⚬ (Need |*| A) =
    id                                               [  Need        |*|            A  ]
      .<.snd(A.signalNeg).<(|*|.assocLR)        .from[ (Need        |*|  Need) |*| A  ]
      .<.fst(selectNeed)                        .from[ (Need        |&|  Need) |*| A  ]
      .<(coDistributeR)                         .from[ (Need |*| A) |&| (Need  |*| A) ]
      .<(|&|.bimap(A.awaitNeg, A.awaitNeg))     .from[           A  |&|            A  ]

  def selectAgainstR[A](implicit A: SignalingJunction.Negative[A]): (A |&| A) -⚬ (A |*| Need) =
    |&|.swap > selectAgainstL > swap

  def raceSignaledOrNot[A](implicit A: SignalingJunction.Positive[A]): A -⚬ (A |+| A) =
    id                                           [  A                             ]
      .>(A.signalPosSnd)                      .to[  A |*|  Done                   ]
      .>.snd(introSnd(done))                  .to[  A |*| (Done  |*|        Done) ]
      .>.snd(raceDone)                        .to[  A |*| (Done  |+|        Done) ]
      .distributeL                            .to[ (A |*|  Done) |+| (A |*| Done) ]
      .bimap(A.awaitPosSnd, A.awaitPosSnd)    .to[  A           |+|  A            ]

  def selectSignaledOrNot[A](implicit A: SignalingJunction.Negative[A]): (A |&| A) -⚬ A =
    id                                           [  A            |&|  A           ]
      .bimap(A.awaitNegSnd, A.awaitNegSnd)    .to[ (A |*|  Need) |&| (A |*| Need) ]
      .coDistributeL                          .to[  A |*| (Need  |&|        Need) ]
      .>.snd(selectNeed)                      .to[  A |*| (Need  |*|        Need) ]
      .>.snd(elimSnd(need))                   .to[  A |*|  Need                   ]
      .>(A.signalNegSnd)                      .to[  A                             ]

  trait Getter[S, A] { self =>
    def getL[B](that: Getter[A, B])(implicit B: Cosemigroup[B]): S -⚬ (B |*| S)

    def extendJunction(implicit A: Junction.Positive[A]): Junction.Positive[S]

    def getL(implicit A: Cosemigroup[A]): S -⚬ (A |*| S) =
      getL(Getter.identity[A])

    def getR(implicit A: Cosemigroup[A]): S -⚬ (S |*| A) =
      getL > swap

    def awaitFst(implicit A: Junction.Positive[A]): (Done |*| S) -⚬ S =
      extendJunction(A).awaitPosFst

    def awaitSnd(implicit A: Junction.Positive[A]): (S |*| Done) -⚬ S =
      swap > awaitFst(A)

    def andThen[B](that: Getter[A, B]): Getter[S, B] =
      new Getter[S, B] {
        override def getL[C](next: Getter[B, C])(implicit C: Cosemigroup[C]): S -⚬ (C |*| S) =
          self.getL(that andThen next)

        override def extendJunction(implicit B: Junction.Positive[B]): Junction.Positive[S] =
          self.extendJunction(that.extendJunction(B))
      }

    def compose[T](that: Getter[T, S]): Getter[T, A] =
      that andThen this

    def |+|[T](that: Getter[T, A]): Getter[S |+| T, A] =
      new Getter[S |+| T, A] {
        override def getL[B](next: Getter[A, B])(implicit B: Cosemigroup[B]): (S |+| T) -⚬ (B |*| (S |+| T)) =
          id[S |+| T].bimap(self.getL(next), that.getL(next)) > factorL

        override def extendJunction(implicit A: Junction.Positive[A]): Junction.Positive[S |+| T] =
          new Junction.Positive[S |+| T] {
            override def awaitPosFst: (Done |*| (S |+| T)) -⚬ (S |+| T) =
              distributeL.bimap(self.awaitFst(A), that.awaitFst(A))
          }
      }
  }

  object Getter {
    def identity[A]: Getter[A, A] =
      new Getter[A, A] {
        override def getL[B](that: Getter[A, B])(implicit B: Cosemigroup[B]): A -⚬ (B |*| A) =
          that.getL

        override def getL(implicit A: Cosemigroup[A]): A -⚬ (A |*| A) =
          A.split

        override def andThen[B](that: Getter[A, B]): Getter[A, B] =
          that

        override def extendJunction(implicit A: Junction.Positive[A]): Junction.Positive[A] =
          A
      }
  }

  trait Lens[S, A] extends Getter[S, A] {
    def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| S) -⚬ (Y |*| S)

    def read[Y](f: A -⚬ (Y |*| A)): S -⚬ (Y |*| S) =
      introFst[S] > modify[One, Y](elimFst > f)

    def write[X](f: (X |*| A) -⚬ A): (X |*| S) -⚬ S =
      modify[X, One](f > introFst) > elimFst

    override def getL[B](that: Getter[A, B])(implicit B: Cosemigroup[B]): S -⚬ (B |*| S) =
      read(that.getL)

    override def extendJunction(implicit A: Junction.Positive[A]): Junction.Positive[S] =
      new Junction.Positive[S] {
        def awaitPosFst: (Done |*| S) -⚬ S = write(A.awaitPosFst)
      }

    def andThen[B](that: Lens[A, B]): Lens[S, B] =
      new Lens[S, B] {
        def modify[X, Y](f: (X |*| B) -⚬ (Y |*| B)): (X |*| S) -⚬ (Y |*| S) =
          Lens.this.modify(that.modify(f))
      }

    def compose[T](that: Lens[T, S]): Lens[T, A] =
      that andThen this

    def |+|[T](that: Lens[T, A]): Lens[S |+| T, A] =
      new Lens[S |+| T, A] {
        def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| (S |+| T)) -⚬ (Y |*| (S |+| T)) =
          distributeL[X, S, T].bimap(Lens.this.modify(f), that.modify(f)) > factorL
      }
  }

  object Lens {
    def rec[F[_]]: Lens[Rec[F], F[Rec[F]]] =
      new Lens[Rec[F], F[Rec[F]]] {
        def modify[X, Y](f: (X |*| F[Rec[F]]) -⚬ (Y |*| F[Rec[F]])): (X |*| Rec[F]) -⚬ (Y |*| Rec[F]) =
          id[X |*| Rec[F]]
            .>.snd(unpack)
            .>(f)
            .>.snd(pack)
      }
  }

  trait Transportive[F[_]] extends Functor[F] {
    def inL[A, B]: (A |*| F[B]) -⚬ F[A |*| B]
    def outL[A, B]: F[A |*| B] -⚬ (A |*| F[B])

    def inR[A, B]: (F[A] |*| B) -⚬ F[A |*| B] =
      swap[F[A], B] > inL > lift(swap[B, A])

    def outR[A, B]: F[A |*| B] -⚬ (F[A] |*| B) =
      lift(swap[A, B]) > outL > swap[B, F[A]]

    def getL[A](implicit A: Cosemigroup[A]): F[A] -⚬ (A |*| F[A]) =
      lift(A.split) > outL

    def getR[A](implicit A: Cosemigroup[A]): F[A] -⚬ (F[A] |*| A) =
      getL[A] > swap

    def lens[A]: Lens[F[A], A] = new Lens[F[A], A] {
      def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| F[A]) -⚬ (Y |*| F[A]) =
        inL > lift(f) > outL
    }
  }

  type Id[A] = A

  implicit val idFunctor: Transportive[Id] = new Transportive[Id] {
    def lift[A, B](f: A -⚬ B): Id[A] -⚬ Id[B] = f
    def inL[A, B]: (A |*| Id[B]) -⚬ Id[A |*| B] = id
    def outL[A, B]: Id[A |*| B] -⚬ (A |*| Id[B]) = id
  }

  object |*| {
    def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C)) = dsl.assocLR
    def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C) = dsl.assocRL

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |*| C) -⚬ (B |*| D) =
      par(f, g)

    val bifunctor: Bifunctor[|*|] =
      new Bifunctor[|*|] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |*| C) -⚬ (B |*| D) =
          bimap(f, g)
      }

    /** Pair is covariant in the first argument. */
    def fst[B]: Transportive[λ[x => x |*| B]] =
      new Transportive[λ[x => x |*| B]] {
        def lift[A1, A2](f: A1 -⚬ A2): (A1 |*| B) -⚬ (A2 |*| B) = par(f, id)
        def inL[A1, A2]: (A1 |*| (A2 |*| B)) -⚬ ((A1 |*| A2) |*| B) = assocRL
        def outL[A1, A2]: ((A1 |*| A2) |*| B) -⚬ (A1 |*| (A2 |*| B)) = assocLR
      }

    /** Pair is covariant in the second argument. */
    def snd[A]: Transportive[λ[x => A |*| x]] =
      new Transportive[λ[x => A |*| x]] {
        def lift[B1, B2](f: B1 -⚬ B2): (A |*| B1) -⚬ (A |*| B2) = par(id, f)
        def inL[B1, B2]: (B1 |*| (A |*| B2)) -⚬ (A |*| (B1 |*| B2)) =
          assocRL[B1, A, B2].>.fst(swap).assocLR
        def outL[B1, B2]: (A |*| (B1 |*| B2)) -⚬ (B1 |*| (A |*| B2)) =
          assocRL[A, B1, B2].>.fst(swap).assocLR
      }
  }

  object |+| {
    def assocLR[A, B, C]: ((A |+| B) |+| C) -⚬ (A |+| (B |+| C)) =
      either(either(injectL, andThen(injectL, injectR)), andThen(injectR, injectR))

    def assocRL[A, B, C]: (A |+| (B |+| C)) -⚬ ((A |+| B) |+| C) =
      either(andThen(injectL, injectL), either(andThen(injectR, injectL), injectR))

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |+| C )-⚬ (B |+| D) =
      either(f > injectL, g > injectR)

    def swap[A, B]: (A |+| B) -⚬ (B |+| A) =
      either(injectR, injectL)

    def IXI[A, B, C, D]: ((A |+| B) |+| (C |+| D)) -⚬ ((A |+| C) |+| (B |+| D)) =
      either(
        either(injectL ∘ injectL, injectR ∘ injectL),
        either(injectL ∘ injectR, injectR ∘ injectR),
      )


    val bifunctor: Bifunctor[|+|] =
      new Bifunctor[|+|] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |+| C )-⚬ (B |+| D) =
          bimap(f, g)
      }

    /** Disjoint union is covariant in the left argument. */
    def left[B]: Functor[λ[x => x |+| B]] =
      bifunctor.fst[B]

    /** Disjoint union is covariant in the right argument. */
    def right[A]: Functor[λ[x => A |+| x]] =
      bifunctor.snd[A]
  }

  object |&| {
    def assocLR[A, B, C]: ((A |&| B) |&| C) -⚬ (A |&| (B |&| C)) =
      choice(andThen(chooseL, chooseL), choice(andThen(chooseL, chooseR), chooseR))

    def assocRL[A, B, C]: (A |&| (B |&| C)) -⚬ ((A |&| B) |&| C) =
      choice(choice(chooseL, andThen(chooseR, chooseL)), andThen(chooseR, chooseR))

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |&| C) -⚬ (B |&| D) =
      choice(chooseL > f, chooseR > g)

    def swap[A, B]: (A |&| B) -⚬ (B |&| A) =
      choice(chooseR, chooseL)

    def IXI[A, B, C, D]: ((A |&| B) |&| (C |&| D)) -⚬ ((A |&| C) |&| (B |&| D)) =
      choice(
        choice(chooseL > chooseL, chooseR > chooseL),
        choice(chooseL > chooseR, chooseR > chooseR),
      )

    val bifunctor: Bifunctor[|&|] =
      new Bifunctor[|&|] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |&| C) -⚬ (B |&| D) =
          bimap(f, g)
      }

    /** Choice is covariant in the left argument. */
    def left[B]: Functor[λ[x => x |&| B]] =
      bifunctor.fst[B]

    /** Choice is covariant in the right argument. */
    def right[A]: Functor[λ[x => A |&| x]] =
      bifunctor.snd[A]
  }

  implicit def fstFunctor[B]: Transportive[λ[x => x |*| B]] = |*|.fst[B]
  implicit def sndFunctor[A]: Transportive[λ[x => A |*| x]] = |*|.snd[A]

  implicit val pairBifunctor: Bifunctor[|*|] = |*|.bifunctor

  implicit val eitherBifunctor: Bifunctor[|+|] = |+|.bifunctor

  implicit val choiceBifunctor: Bifunctor[|&|] = |&|.bifunctor

  implicit class LinearFunctionOps[A, B](self: A -⚬ B) {
    /** No-op used for documentation purposes: explicitly states the input type of this linear function. */
    def from[Z](implicit ev: A =:= Z): Z -⚬ B = ev.substituteCo[λ[x => x -⚬ B]](self)

    /** No-op used for documentation purposes: explicitly states the output type of this linear function. */
    def to[C](implicit ev: B =:= C): A -⚬ C = ev.substituteCo(self)

    /** No-op used for documentation purposes: explicitly states the full type of this linear function. */
    def as[C](implicit ev: (A -⚬ B) =:= C): C = ev(self)

    def ∘[Z](g: Z -⚬ A): Z -⚬ B = dsl.andThen(g, self)

    def bimap[F[_, _]]: BimapSyntax[F, A, B] =
      new BimapSyntax[F, A, B](self)

    def injectL[C]: A -⚬ (B |+| C) =
      dsl.andThen(self, dsl.injectL)

    def injectR[C]: A -⚬ (C |+| B) =
      dsl.andThen(self, dsl.injectR)

    def either[B1, B2, C](f: B1 -⚬ C, g: B2 -⚬ C)(implicit ev: B =:= (B1 |+| B2)): A -⚬ C =
      dsl.andThen(ev.substituteCo(self), dsl.either(f, g))

    def chooseL[B1, B2](implicit ev: B =:= (B1 |&| B2)): A -⚬ B1 =
      ev.substituteCo(self) > dsl.chooseL

    def chooseR[B1, B2](implicit ev: B =:= (B1 |&| B2)): A -⚬ B2 =
      ev.substituteCo(self) > dsl.chooseR

    def choice[C, D](f: B -⚬ C, g: B -⚬ D): A -⚬ (C |&| D) =
      self > dsl.choice(f, g)

    def par[B1, B2, C, D](f: B1 -⚬ C, g: B2 -⚬ D)(implicit ev: B =:= (B1 |*| B2)): A -⚬ (C |*| D) =
      ev.substituteCo(self) > dsl.par(f, g)

    def elimFst[B2](implicit ev: B =:= (One |*| B2)): A -⚬ B2 =
      ev.substituteCo(self) > dsl.elimFst

    def elimFst[B1, B2](f: B1 -⚬ One)(implicit ev: B =:= (B1 |*| B2)): A -⚬ B2 =
      ev.substituteCo(self) > dsl.elimFst(f)

    def elimSnd[B1](implicit ev: B =:= (B1 |*| One)): A -⚬ B1 =
      ev.substituteCo(self) > dsl.elimSnd

    def elimSnd[B1, B2](f: B2 -⚬ One)(implicit ev: B =:= (B1 |*| B2)): A -⚬ B1 =
      ev.substituteCo(self) > dsl.elimSnd(f)

    def introFst: A -⚬ (One |*| B) =
      self > dsl.introFst

    def introFst[C](f: One -⚬ C): A -⚬ (C |*| B) =
      self > dsl.introFst(f)

    def introSnd: A -⚬ (B |*| One) =
      self > dsl.introSnd

    def introSnd[C](f: One -⚬ C): A -⚬ (B |*| C) =
      self > dsl.introSnd(f)

    def swap[B1, B2](implicit ev: B =:= (B1 |*| B2)): A -⚬ (B2 |*| B1) =
      ev.substituteCo(self) > dsl.swap

    def distributeL[B1, B2, B3](implicit ev: B =:= (B1 |*| (B2 |+| B3))): A -⚬ ((B1 |*| B2) |+| (B1 |*| B3)) =
      ev.substituteCo(self) > dsl.distributeL

    def distributeR[B1, B2, B3](implicit ev: B =:= ((B1 |+| B2) |*| B3)): A -⚬ ((B1 |*| B3) |+| (B2 |*| B3)) =
      ev.substituteCo(self) > dsl.distributeR

    def factorL[C, D1, D2](implicit ev: B =:= ((C |*| D1) |+| (C |*| D2))): A -⚬ (C |*| (D1 |+| D2)) =
      ev.substituteCo(self) > dsl.factorL

    def factorR[C1, C2, D](implicit ev: B =:= ((C1 |*| D) |+| (C2 |*| D))): A -⚬ ((C1 |+| C2) |*| D) =
      ev.substituteCo(self) > dsl.factorR

    def coDistributeL[B1, B2, B3](implicit ev: B =:= ((B1 |*| B2) |&| (B1 |*| B3))): A -⚬ (B1 |*| (B2 |&| B3)) =
      ev.substituteCo(self) > dsl.coDistributeL

    def coDistributeR[B1, B2, B3](implicit ev: B =:= ((B1 |*| B3) |&| (B2 |*| B3))): A -⚬ ((B1 |&| B2) |*| B3) =
      ev.substituteCo(self) > dsl.coDistributeR

    def coFactorL[B1, B2, B3](implicit ev: B =:= (B1 |*| (B2 |&| B3))): A -⚬ ((B1 |*| B2) |&| (B1 |*| B3)) =
      ev.substituteCo(self) > dsl.coFactorL

    def coFactorR[B1, B2, B3](implicit ev: B =:= ((B1 |&| B2) |*| B3)): A -⚬ ((B1 |*| B3) |&| (B2 |*| B3)) =
      ev.substituteCo(self) > dsl.coFactorR

    def pack[F[_]](implicit ev: B =:= F[Rec[F]]): A -⚬ Rec[F] =
      ev.substituteCo(self) > dsl.pack[F]

    def unpack[F[_]](implicit ev: B =:= Rec[F]): A -⚬ F[Rec[F]] =
      ev.substituteCo(self) > dsl.unpack[F]

    def race[B1: Signaling.Positive, B2: Signaling.Positive, C](
      caseFstWins: (B1 |*| B2) -⚬ C,
      caseSndWins: (B1 |*| B2) -⚬ C,
    )(implicit
      ev: B =:= (B1 |*| B2),
    ): A -⚬ C =
      ev.substituteCo(self) > lib.race(caseFstWins, caseSndWins)

    def select[C1: Signaling.Negative, C2: Signaling.Negative](
      caseFstWins: B -⚬ (C1 |*| C2),
      caseSndWins: B -⚬ (C1 |*| C2),
    ): A -⚬ (C1 |*| C2) =
      self > lib.select(caseFstWins, caseSndWins)

    /** Focuses on function's output. */
    def > : FocusedCo[[x] =>> A -⚬ x, B] =
      new FocusedCo[[x] =>> A -⚬ x, B](self)

    /** Focuses on function's input. */
    def < : FocusedContra[[x] =>> x -⚬ B, A] =
      new FocusedContra[[x] =>> x -⚬ B, A](self)
  }

  implicit class LinearFunctionToPairOps[A, B1, B2](self: A -⚬ (B1 |*| B2)) {
    def assocLR[X, Y](implicit ev: B1 =:= (X |*| Y)): A -⚬ (X |*| (Y |*| B2)) =
      ev.substituteCo[λ[x => A -⚬ (x |*| B2)]](self) > |*|.assocLR

    def assocRL[X, Y](implicit ev: B2 =:= (X |*| Y)): A -⚬ ((B1 |*| X) |*| Y) =
      ev.substituteCo[λ[x => A -⚬ (B1 |*| x)]](self) > |*|.assocRL

    def awaitFst(neglect: B1 -⚬ Done)(implicit j: Junction.Positive[B2]): A -⚬ B2 =
      self > par(neglect, id[B2]) > j.awaitPosFst

    def awaitSnd(neglect: B2 -⚬ Done)(implicit j: Junction.Positive[B1]): A -⚬ B1 =
      self > par(id[B1], neglect) > j.awaitPosSnd

    def awaitFst(implicit ev: B1 =:= Done, j: Junction.Positive[B2]): A -⚬ B2 = {
      type F[X] = A -⚬ (X |*| B2)
      ev.substituteCo[F](self) > j.awaitPosFst
    }

    def awaitSnd(implicit ev: B2 =:= Done, j: Junction.Positive[B1]): A -⚬ B1 = {
      type F[X] = A -⚬ (B1 |*| X)
      ev.substituteCo[F](self) > j.awaitPosSnd
    }
  }

  implicit class LinearFunctionToPlusOps[A, B1, B2](self: A -⚬ (B1 |+| B2)) {
    def assocLR[X, Y](implicit ev: B1 =:= (X |+| Y)): A -⚬ (X |+| (Y |+| B2)) =
      ev.substituteCo[λ[x => A -⚬ (x |+| B2)]](self) > |+|.assocLR

    def assocRL[X, Y](implicit ev: B2 =:= (X |+| Y)): A -⚬ ((B1 |+| X) |+| Y) =
      ev.substituteCo[λ[x => A -⚬ (B1 |+| x)]](self) > |+|.assocRL
  }

  class BimapSyntax[F[_, _], A, B](self: A -⚬ B) {
    def apply[B1, B2, C, D](
      f: B1 -⚬ C,
      g: B2 -⚬ D,
    )(implicit
      ev: B =:= F[B1, B2],
      F: Bifunctor[F],
    ): A -⚬ F[C, D] =
      dsl.andThen(ev.substituteCo(self), F.lift(f, g))
  }

  /** Focused on `B` in `F[B]`, where `B` is in a covariant position. */
  class FocusedCo[F[_], B](f: F[B])(implicit F: Externalizer[F]) {
    def map[C](g: B -⚬ C): F[C] = F.lift(g)(f)

    /** Alias for [[map]]. */
    def apply[C](g: B -⚬ C): F[C] = map(g)

    def subst[C](implicit ev: B =:= C): F[C] =
      ev.substituteCo(f)

    def unsubst[C](implicit ev: C =:= B): F[C] =
      ev.substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(implicit ev: B =:= G[C]): FocusedCo[λ[x => F[G[x]]], C] =
      new FocusedCo[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ∘ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(implicit ev: B =:= G[C]): FocusedContra[λ[x => F[G[x]]], C] =
      new FocusedContra[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ∘ G)

    def co[G[_]](implicit G: Functor[G], U: Unapply[B, G]): FocusedCo[λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(U.ev)

    def contra[G[_]](implicit G: ContraFunctor[G], U: Unapply[B, G]): FocusedContra[λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(U.ev)

    def bi[G[_, _]](implicit G: Bifunctor[G], U: Unapply2[B, G]): FocusedBi[λ[(x, y) => F[G[x, y]]], U.A, U.B] =
      new FocusedBi[λ[(x, y) => F[G[x, y]]], U.A, U.B](U.ev.substituteCo(f))(F ∘ G)

    def injectL[C]: F[B |+| C] = F.lift(dsl.injectL)(f)
    def injectR[C]: F[C |+| B] = F.lift(dsl.injectR)(f)

    def signalFst(implicit B: Signaling.Positive[B]): F[Done |*| B] =
      map(B.signalPosFst)

    def signalSnd(implicit B: Signaling.Positive[B]): F[B |*| Done] =
      map(B.signalPosSnd)
  }

  class FocusedBi[F[_, _], B1, B2](f: F[B1, B2])(F: BiExternalizer[F]) {
    def map[C1, C2](g: B1 -⚬ C1, h: B2 -⚬ C2): F[C1, C2] =
      F.lift(g, h)(f)

    def fst: FocusedCo[F[*, B2], B1] =
      new FocusedCo[F[*, B2], B1](f)(F.fst)

    def snd: FocusedCo[F[B1, *], B2] =
      new FocusedCo[F[B1, *], B2](f)(F.snd)
  }

  implicit class FocusedOnPairCo[F[_], B1, B2](f: FocusedCo[F, B1 |*| B2]) {
    def fst: FocusedCo[λ[x => F[x |*| B2]], B1] =
      f.zoomCo(|*|.fst[B2])

    def snd: FocusedCo[λ[x => F[B1 |*| x]], B2] =
      f.zoomCo(|*|.snd[B1])

    def assocLR[X, Y](implicit ev: B1 =:= (X |*| Y)): F[X |*| (Y |*| B2)] = {
      val g: FocusedCo[F, (X |*| Y) |*| B2] =
        ev.substituteCo[λ[x => FocusedCo[F, x |*| B2]]](f)
      g(|*|.assocLR)
    }

    def assocRL[X, Y](implicit ev: B2 =:= (X |*| Y)): F[(B1 |*| X) |*| Y] = {
      val g: FocusedCo[F, B1 |*| (X |*| Y)] =
        ev.substituteCo[λ[x => FocusedCo[F, B1 |*| x]]](f)
      g(|*|.assocRL)
    }

    def awaitFst(neglect: B1 -⚬ Done)(implicit j: Junction.Positive[B2]): F[B2] =
      f(par(neglect, id[B2]) > j.awaitPosFst)

    def awaitSnd(neglect: B2 -⚬ Done)(implicit j: Junction.Positive[B1]): F[B1] =
      f(par(id[B1], neglect) > j.awaitPosSnd)
  }

  implicit class FocusedOnDoneTimesCo[F[_], B2](f: FocusedCo[F, Done |*| B2])(implicit j: Junction.Positive[B2]) {
    def awaitFst: F[B2] = f(j.awaitPosFst)
  }

  implicit class FocusedOnTimesDoneCo[F[_], B1](f: FocusedCo[F, B1 |*| Done])(implicit j: Junction.Positive[B1]) {
    def awaitSnd: F[B1] = f(j.awaitPosSnd)
  }

  implicit class FocusedOnPlusCo[F[_], B1, B2](f: FocusedCo[F, B1 |+| B2]) {
    def left: FocusedCo[λ[x => F[x |+| B2]], B1] =
      f.zoomCo(|+|.left[B2])

    def right: FocusedCo[λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(|+|.right[B1])

    def assocLR[X, Y](implicit ev: B1 =:= (X |+| Y)): F[X |+| (Y |+| B2)] = {
      val g: FocusedCo[F, (X |+| Y) |+| B2] =
        ev.substituteCo[λ[x => FocusedCo[F, x |+| B2]]](f)
      g(|+|.assocLR)
    }

    def assocRL[X, Y](implicit ev: B2 =:= (X |+| Y)): F[(B1 |+| X) |+| Y] = {
      val g: FocusedCo[F, B1 |+| (X |+| Y)] =
        ev.substituteCo[λ[x => FocusedCo[F, B1 |+| x]]](f)
      g(|+|.assocRL)
    }
  }

  implicit class FocusedOnChoiceCo[F[_], B1, B2](f: FocusedCo[F, B1 |&| B2]) {
    def choiceL: FocusedCo[λ[x => F[x |&| B2]], B1] =
      f.zoomCo(|&|.left[B2])

    def choiceR: FocusedCo[λ[x => F[B1 |&| x]], B2] =
      f.zoomCo(|&|.right[B1])

    def assocLR[X, Y](implicit ev: B1 =:= (X |&| Y)): F[X |&| (Y |&| B2)] = {
      val g: FocusedCo[F, (X |&| Y) |&| B2] =
        ev.substituteCo[λ[x => FocusedCo[F, x |&| B2]]](f)
      g(|&|.assocLR)
    }

    def assocRL[X, Y](implicit ev: B2 =:= (X |&| Y)): F[(B1 |&| X) |&| Y] = {
      val g: FocusedCo[F, B1 |&| (X |&| Y)] =
        ev.substituteCo[λ[x => FocusedCo[F, B1 |&| x]]](f)
      g(|&|.assocRL)
    }
  }

  /** Focused on `B` in the output `F[B]` of linear function `A -⚬ F[B]`, where `B` is in a contravariant position. */
  class FocusedContra[F[_], B](f: F[B])(implicit F: ContraExternalizer[F]) {
    def contramap[A](g: A -⚬ B): F[A] =
      F.lift(g)(f)

    /** Alias for [[contramap]]. */
    def apply[A](g: A -⚬ B): F[A] =
      contramap(g)

    def subst[C](implicit ev: B =:= C): F[C] =
      ev.substituteCo(f)

    def unsubst[C](implicit ev: C =:= B): F[C] =
      ev.substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(implicit ev: B =:= G[C]): FocusedContra[λ[x => F[G[x]]], C] =
      new FocusedContra[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ∘ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(implicit ev: B =:= G[C]): FocusedCo[λ[x => F[G[x]]], C] =
      new FocusedCo[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ∘ G)

    def co[G[_]](implicit G: Functor[G], U: Unapply[B, G]): FocusedContra[λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(U.ev)

    def contra[G[_]](implicit G: ContraFunctor[G], U: Unapply[B, G]): FocusedCo[λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(U.ev)
  }

  implicit class FocusedOnPairContra[A, F[_], B1, B2](f: FocusedContra[F, B1 |*| B2]) {
    def fst: FocusedContra[λ[x => F[x |*| B2]], B1] =
      f.zoomCo(|*|.fst[B2])

    def snd: FocusedContra[λ[x => F[B1 |*| x]], B2] =
      f.zoomCo(|*|.snd[B1])
  }

  implicit class FocusedOnPlusContra[A, F[_], B1, B2](f: FocusedContra[F, B1 |+| B2]) {
    def left: FocusedContra[λ[x => F[x |+| B2]], B1] =
      f.zoomCo(|+|.left[B2])

    def right: FocusedContra[λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(|+|.right[B1])
  }

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
      .assocLR                  .to[ A |*| (B |*| (C |*| D)) ]
      .>.snd.assocRL            .to[ A |*| ((B |*| C) |*| D) ]
      .>.snd.fst(swap)          .to[ A |*| ((C |*| B) |*| D) ]
      .>.snd.assocLR            .to[ A |*| (C |*| (B |*| D)) ]
      .assocRL                  .to[ (A |*| C) |*| (B |*| D) ]

  def IX[A, B, C]: ((A|*|B)|*| C) -⚬
    //               |    \   /
    //               |     \ /
    //               |      X
    //               |     / \
    //               |    /   \
                   ((A|*|C)|*| B) =
    |*|.assocLR[A, B, C] > par(id, swap) > |*|.assocRL

  def XI[A, B, C]: (A |*|(B|*|C)) -⚬
    //               \   /    |
    //                \ /     |
    //                 X      |
    //                / \     |
    //               /   \    |
                   (B |*|(A|*|C)) =
    |*|.assocRL[A, B, C] > par(swap, id) > |*|.assocLR

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
      .distributeR             .to[(A |*| (C |&| D)) |+| (B |*| (C |&| D))]
      .>.left.snd(chooseL)     .to[(A |*|  C       ) |+| (B |*| (C |&| D))]
      .>.right.snd(chooseR)    .to[(A |*|  C       ) |+| (B |*|        D )]

  /** From the choice ''available'' on the left (`A |&| B`), choose the one corresponding to the choice ''made''
    * on the right (`C |+| D`): if on the right there is `C`, choose `A`, if on the right there is `D`, choose `B`.
    */
  def matchingChoiceRL[A, B, C, D]: ((A |&| B) |*| (C |+| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |&| B) |*| (C |+| D)]
      .distributeL             .to[((A |&| B) |*| C) |+| ((A |&| B) |*| D)]
      .>.left.fst(chooseL)     .to[( A        |*| C) |+| ((A |&| B) |*| D)]
      .>.right.fst(chooseR)    .to[( A        |*| C) |+| (       B  |*| D)]

  /** Present a choice between two pairs (`(A |*| B) |&| (C |*| D)`) as a choice (`A |&| C`) between the first
    * parts of the respective pairs and on the side provide the other part of the chosen input pair, i.e. either
    * `B` or `D` (`B |+| D`).
    */
  def subordinateSnd[A, B, C, D]: ((A |*| B) |&| (C |*| D)) -⚬ ((A |&| C) |*| (B |+| D)) =
    id                                 [ (A |*|  B       ) |&| (C |*|        D ) ]
      .>.choiceL.snd.injectL[D]     .to[ (A |*| (B |+| D)) |&| (C |*|        D ) ]
      .>.choiceR.snd.injectR[B]     .to[ (A |*| (B |+| D)) |&| (C |*| (B |+| D)) ]
      .coDistributeR

  /** Present a choice between two pairs (`(A |*| B) |&| (C |*| D)`) as a choice (`B |&| D`) between the second
    * parts of the respective pairs and on the side provide the other part of the chosen input pair, i.e. either
    * `A` or `C` (`A |+| C`).
    */
  def subordinateFst[A, B, C, D]: ((A |*| B) |&| (C |*| D)) -⚬ ((A |+| C) |*| (B |&| D)) =
    id                                 [ ( A        |*|  B) |&| (       C  |*| D) ]
      .>.choiceL.fst.injectL[C]     .to[ ((A |+| C) |*|  B) |&| (       C  |*| D) ]
      .>.choiceR.fst.injectR[A]     .to[ ((A |+| C) |*|  B) |&| ((A |+| C) |*| D) ]
      .coDistributeL                .to[  (A |+| C) |*| (B  |&|                D) ]

  /** Notifies when the [[|+|]] is decided _and_ the present side notifies using the respective given function. */
  def notifyEitherAndSides[A, B](
    notifyL: A -⚬ (Ping |*| A),
    notifyR: B -⚬ (Ping |*| B),
  ): (A |+| B) -⚬ (Ping |*| (A |+| B)) =
    id                                           [                      A  |+|           B   ]
      .>(|+|.bimap(notifyL, notifyR))         .to[            (Ping |*| A) |+| (Ping |*| B)  ]
      .>(notifyEither)                        .to[  Ping |*| ((Ping |*| A) |+| (Ping |*| B)) ]
      .>.snd(factorL)                         .to[  Ping |*| (Ping  |*| (A |+|           B)) ]
      .>(assocRL)                             .to[ (Ping |*|  Ping) |*| (A |+|           B)  ]
      .>.fst(joinPing)                        .to[      Ping        |*| (A |+|           B)  ]

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
    id                                       [                      A  |&|           B   ]
      .<(|&|.bimap(notifyL, notifyR))   .from[            (Pong |*| A) |&| (Pong |*| B)  ]
      .<(notifyChoice)                  .from[  Pong |*| ((Pong |*| A) |&| (Pong |*| B)) ]
      .<.snd(coFactorL)                 .from[  Pong |*| (Pong  |*| (A |&|           B)) ]
      .<(assocLR)                       .from[ (Pong |*|  Pong) |*| (A |&|           B)  ]
      .<.fst(joinPong)                  .from[      Pong        |*| (A |&|           B)  ]

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
    id                                                     [ Done |*| (                    A   |&| B) ]
      .>.snd.choiceL(introFst(lInvertSignal).assocLR)   .to[ Done |*| ((Need |*| (Done |*| A)) |&| B) ]
      .>.snd(chooseLWhenNeed)                           .to[ Done |*|  (Need |*| (Done |*| A))        ]
      .assocRL.elimFst(rInvertSignal)                   .to[                      Done |*| A          ]

  def chooseRWhenDone[A, B]: (Done |*| (A |&| B)) -⚬ (Done |*| B) =
    id                                                     [ Done |*| (A |&|                     B  ) ]
      .>.snd.choiceR(introFst(lInvertSignal).assocLR)   .to[ Done |*| (A |&| (Need |*| (Done |*| B))) ]
      .>.snd(chooseRWhenNeed)                           .to[ Done |*|        (Need |*| (Done |*| B))  ]
      .assocRL.elimFst(rInvertSignal)                   .to[                            Done |*| B    ]

  def injectLWhenNeed[A, B]: (Need |*| A) -⚬ (Need |*| (A |+| B)) =
    id                                                     [                      Need |*| A   ]
      .introFst(lInvertSignal).assocLR                  .to[ Need |*|  (Done |*| (Need |*| A)) ]
      .>.snd(injectLWhenDone)                           .to[ Need |*| ((Done |*| (Need |*| A)) |+| B) ]
      .>.snd.left(|*|.assocRL.elimFst(rInvertSignal))   .to[ Need |*| (                    A   |+| B) ]

  def injectRWhenNeed[A, B]: (Need |*| B) -⚬ (Need |*| (A |+| B)) =
    id                                                     [                            Need |*| B    ]
      .introFst(lInvertSignal).assocLR                  .to[ Need |*|        (Done |*| (Need |*| B))  ]
      .>.snd(injectRWhenDone)                           .to[ Need |*| (A |+| (Done |*| (Need |*| B))) ]
      .>.snd.right(|*|.assocRL.elimFst(rInvertSignal))  .to[ Need |*| (A |+|                     B  ) ]

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
      .distributeL                                                .to[ (Done |*|  A) |+| (Done |*| B) ]
      .either(injectLWhenDone, injectRWhenDone)                   .to[ (Done |*|  A) |+| (Done |*| B) ]

  def delayChoiceUntilNeed[A, B]: ((Need |*| A) |&| (Need |*| B)) -⚬ (Need |*| (A |&| B)) =
    id                                                               [ (Need |*|  A) |&| (Need |*| B) ]
      .choice(chooseLWhenNeed, chooseRWhenNeed)                   .to[ (Need |*|  A) |&| (Need |*| B) ]
      .coDistributeL                                              .to[  Need |*| (A  |&|           B) ]

  def delayEitherUntilNeed[A, B]: ((Need |*| A) |+| (Need |*| B)) -⚬ (Need |*| (A |+| B)) =
    id                                                               [ (Need |*|  A) |+| (Need |*| B) ]
      .either(injectLWhenNeed, injectRWhenNeed)                   .to[  Need |*| (A  |+|           B) ]

  def delayChoiceUntilDone[A, B]: (Done |*| (A |&| B)) -⚬ ((Done |*| A) |&| (Done |*| B)) =
    id                                                               [  Done |*| (A  |&|           B) ]
      .choice(chooseLWhenDone[A, B], chooseRWhenDone[A, B])       .to[ (Done |*|  A) |&| (Done |*| B) ]

  /** Injects `A` from the the second in-port to the left side of the `|+|` in the out-port, but only after
    * the `Done` signal from the first in-port arrives. That means that the consumer of `A |+| B` will see it
    * as undecided until the `Done` signal arrives. This is different from `awaitPosFst[A] > injectL[A, B]`,
    * in which the consumer of `A |+| B` knows immediately that it is the left case.
    *
    * This is a convenience method on top of [[injectLWhenDone]] that which absorbs the `Done` signal using
    * the given [[Junction.Positive]].
    */
  def awaitInjectL[A, B](implicit A: Junction.Positive[A]): (Done |*| A) -⚬ (A |+| B) =
    injectLWhenDone.>.left(A.awaitPos)

  /** Analogous to [[joinInjectL]], but injects to the right. */
  def awaitInjectR[A, B](implicit B: Junction.Positive[B]): (Done |*| B) -⚬ (A |+| B) =
    injectRWhenDone.>.right(B.awaitPos)

  /** Chooses the left alternative `A` of the choice `A |&| B`, but only after the `Need` signal from the first
    * out-port arrives. Until then, the producer of `A |&| B` will see it as undecided. This is different from
    * `chooseL[A, B] > awaitNegFst[A]`, in which the producer of `A |&| B` knows immediately that the left side
    * is chosen.
    */
  def awaitChooseL[A, B](implicit A: Junction.Negative[A]): (A |&| B) -⚬ (Need |*| A) =
    id[A |&| B].>.choiceL(A.awaitNeg) > chooseLWhenNeed

  /** Analogous to [[awaitChooseL]], but chooses the right side. */
  def awaitChooseR[A, B](implicit B: Junction.Negative[B]): (A |&| B) -⚬ (Need |*| B) =
    id[A |&| B].>.choiceR(B.awaitNeg) > chooseRWhenNeed

  /** Analogous to [[awaitChooseL]], but awaits a positive (i.e. [[Done]]) signal. */
  def awaitPosChooseL[A, B](implicit A: Junction.Positive[A]): (Done |*| (A |&| B)) -⚬ A =
    par(id, awaitChooseL(Junction.invert(A))).assocRL.elimFst(rInvertSignal)

  /** Analogous to [[awaitChooseR]], but awaits a positive (i.e. [[Done]]) signal. */
  def awaitPosChooseR[A, B](implicit B: Junction.Positive[B]): (Done |*| (A |&| B)) -⚬ B =
    par(id, awaitChooseR(Junction.invert(B))).assocRL.elimFst(rInvertSignal)

  /** Creates a pair of mutually recursive functions. */
  def rec2[A, B, C, D](
    f: (A -⚬ B, C -⚬ D) => A -⚬ B,
    g: (A -⚬ B, C -⚬ D) => C -⚬ D,
  ): (A -⚬ B, C -⚬ D) =
    (
      rec { (ab: A -⚬ B) => f(ab, rec { (cd: C -⚬ D) => g(ab, cd) }) },
      rec { (cd: C -⚬ D) => g(rec { (ab: A -⚬ B) => f(ab, cd) }, cd) },
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
      distributeL.either(caseTrue, caseFalse)

    def switchWithR[A, R](
      caseTrue : (Done |*| A) -⚬ R,
      caseFalse: (Done |*| A) -⚬ R,
    ): (Bool |*| A) -⚬ R =
      distributeR.either(caseTrue, caseFalse)

    def ifThenElse[A, B, C](ifTrue: (Done |*| A) -⚬ B, ifFalse: (Done |*| A) -⚬ C): (Bool |*| A) -⚬ (B |+| C) =
      id                                   [          Bool |*| A           ]
        .distributeR                    .to[ (Done |*| A) |+| (Done |*| A) ]
        .bimap(ifTrue, ifFalse)         .to[        B     |+|        C     ]
  }

  import Bool._

  def testBy[A, B, K: Cosemigroup: Junction.Positive](
    aKey: Getter[A, K],
    bKey: Getter[B, K],
    pred: (K |*| K) -⚬ Bool,
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) = {
    val awaitL: (Done |*| (A |*| B)) -⚬ (A |*| B) =
      (aKey compose |*|.fst[B].lens[A]).awaitFst

    id[A |*| B]
      .par(aKey.getL, bKey.getL)
      .>(IXI)
      .>.fst(pred)
      .>(ifThenElse(awaitL, awaitL))
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
      id[ Compared[A, B] |*| C ]                .to[ ((A |*| B)        |+| ( (A |*| B)        |+|  (A |*| B))) |*| C   ]
        .distributeR.>.right(distributeR)       .to[ ((A |*| B) |*| C) |+| (((A |*| B) |*| C) |+| ((A |*| B)   |*| C)) ]
        .either(caseLt, either(caseEq, caseGt)) .to[                    D                                              ]

    def enrichWith[A, B, C, S, T](
      f: ((A |*| B) |*| C) -⚬ (S |*| T),
    )
    : (Compared[A, B] |*| C) -⚬ Compared[S, T] =
      id[ Compared[A, B] |*| C ]                .to[ ((A |*| B)        |+| ( (A |*| B)        |+|  (A |*| B))) |*| C   ]
        .distributeR.>.right(distributeR)       .to[ ((A |*| B) |*| C) |+| (((A |*| B) |*| C) |+| ((A |*| B)   |*| C)) ]
        .bimap[|+|](f, |+|.bimap(f, f))         .to[     (S |*| T)     |+| (    (S |*| T)     |+|      (S |*| T)     ) ]

    def bifunctorCompared: Bifunctor[Compared] =
      new Bifunctor[Compared] {
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

  import Compared._

  def compareBy[A, B, K1 : PComonoid : Junction.Positive, K2 : PComonoid : Junction.Positive](
    aKey: Getter[A, K1],
    bKey: Getter[B, K2],
  )(implicit
    cmp: Comparable[K1, K2],
  ): (A |*| B) -⚬ Compared[A, B] = {
    cmp.contramap(aKey, bKey).compare
  }

  trait Comparable[A, B] { self =>
    def compare: (A |*| B) -⚬ Compared[A, B]

    def contramap[S, T](
      f: Getter[S, A],
      g: Getter[T, B],
    )(implicit
      A: PComonoid[A],
      B: PComonoid[B],
      AJ: Junction.Positive[A],
      BJ: Junction.Positive[B],
    ): Comparable[S, T] =
      new Comparable[S, T] {
        private val absorb: ((A |*| B) |*| (S |*| T)) -⚬ (S |*| T) =
          id                                 [ (A    |*| B) |*| (S    |*| T) ]
            .>(IXI)                       .to[ (A    |*| S) |*| (B    |*| T) ]
            .>.fst.fst(A.counit)          .to[ (Done |*| S) |*| (B    |*| T) ]
            .>.snd.fst(B.counit)          .to[ (Done |*| S) |*| (Done |*| T) ]
            .par(f.awaitFst, g.awaitFst)  .to[           S  |*|           T  ]

        override def compare: (S |*| T) -⚬ Compared[S, T] = {
          id[ S |*| T ]
            .par(f.getL, g.getL)
            .>(IXI)
            .>.fst(self.compare)
            .>(Compared.enrichWith(absorb))
        }
      }
  }

  def dualSymmetric[A, B](ev: Dual[A, B]): Dual[B, A] = new Dual[B, A] {
    val lInvert: One -⚬ (A |*| B) = andThen(ev.lInvert, swap)
    val rInvert: (B |*| A) -⚬ One = andThen(swap, ev.rInvert)
  }

  implicit def oneSelfDual: Dual[One, One] = new Dual[One, One] {
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
      .par(lInvertA, lInvertB)                .to[ (Ȧ |*| A) |*| (Ḃ |*| B) ]
      .>(IXI)                                 .to[ (Ȧ |*| Ḃ) |*| (A |*| B) ]

  implicit def pairDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |*| B, Ȧ |*| Ḃ] =
    new Dual[A |*| B, Ȧ |*| Ḃ] {
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
      .either(rInvertA, rInvertB)   .to[           One           ]

  def lInvertChoice[A, B, Ȧ, Ḃ](
    lInvertA: One -⚬ (Ȧ |*| A),
    lInvertB: One -⚬ (Ḃ |*| B),
  ): One -⚬ ((Ȧ |&| Ḃ) |*| (A |+| B)) =
    id                                 [           One           ]
      .choice(lInvertA, lInvertB)   .to[ (Ȧ |*| A) |&| (Ḃ |*| B) ]
      .>(subordinateSnd)            .to[ (Ȧ |&| Ḃ) |*| (A |+| B) ]

  implicit def eitherChoiceDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |+| B, Ȧ |&| Ḃ] =
    new Dual[A |+| B, Ȧ |&| Ḃ] {
      val rInvert: ((A |+| B) |*| (Ȧ |&| Ḃ)) -⚬ One =
        rInvertEither(a.rInvert, b.rInvert)

      val lInvert: One -⚬ ((Ȧ |&| Ḃ) |*| (A |+| B)) =
        lInvertChoice(a.lInvert, b.lInvert)
    }

  implicit def choiceEitherDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |&| B, Ȧ |+| Ḃ] =
    dualSymmetric(eitherChoiceDuality(dualSymmetric(a), dualSymmetric(b)))

  implicit def doneNeedDuality: Dual[Done, Need] =
    new Dual[Done, Need] {
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

    def getOrElse[A](f: One -⚬ A): Maybe[A] -⚬ A =
      either(f, id)

    def discard[A](f: A -⚬ One): Maybe[A] -⚬ One =
      either(id, f)

    def discard[A](implicit A: Comonoid[A]): Maybe[A] -⚬ One =
      discard(A.counit)

    def neglect[A](f: A -⚬ Done): Maybe[A] -⚬ Done =
      either(done, f)
  }

  opaque type Optionally[A] = One |&| A
  object Optionally {
    def optOut[A]: Optionally[A] -⚬ One =
      chooseL

    def optIn[A]: Optionally[A] -⚬ A =
      chooseR

    def fromDiscardable[A](discard: A -⚬ One): A -⚬ Optionally[A] =
      choice(discard, id)
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

    def neglect[A](implicit A: PComonoid[A]): PMaybe[A] -⚬ Done =
      neglect(A.counit)

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
      id[One]
        .injectL[A |+| (Multiple[A] |*| Multiple[A])]
        .pack[MultipleF[A, *]]

    def one[A]: A -⚬ Multiple[A] =
      id[A]
        .injectL[Multiple[A] |*| Multiple[A]]
        .injectR[One]
        .pack[MultipleF[A, *]]

    def append[A]: (Multiple[A] |*| Multiple[A]) -⚬ Multiple[A] =
      id[Multiple[A] |*| Multiple[A]]
        .injectR[A]
        .injectR[One]
        .pack[MultipleF[A, *]]

    def switch[A, R](
      case0: One -⚬ R,
      case1: A -⚬ R,
      caseN: (Multiple[A] |*| Multiple[A]) -⚬ R,
    ): Multiple[A] -⚬ R =
      unpack[MultipleF[A, *]] > either(case0, either(case1, caseN))

    def flatten[A]: Multiple[Multiple[A]] -⚬ Multiple[A] = rec { self =>
      switch(
        case0 = zero,
        case1 = id,
        caseN = par(self, self) > append
      )
    }

    implicit def monoidMultiple[A]: Monoid[Multiple[A]] =
      new Monoid[Multiple[A]] {
        def unit    :                           One -⚬ Multiple[A] = Multiple.zero
        def combine : (Multiple[A] |*| Multiple[A]) -⚬ Multiple[A] = Multiple.append
      }

    implicit val monadMultiple: Monad[Multiple] =
      new Monad[Multiple] {
        def pure[A]    :                     A -⚬ Multiple[A] = Multiple.one
        def flatten[A] : Multiple[Multiple[A]] -⚬ Multiple[A] = Multiple.flatten
      }
  }

  private type UnlimitedF[A, X] = One |&| (A |&| (X |*| X))

  /** Unlimited supply of `A`s. The consumer chooses how many `A`s to consume. */
  opaque type Unlimited[A] = Rec[UnlimitedF[A, *]]
  object Unlimited {
    private def unpack[A]: Unlimited[A] -⚬ UnlimitedF[A, Unlimited[A]] =
      dsl.unpack

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
        .>(Endless.unfold(f))             .to[  Endless[A]  |*| S ]
        .>.fst(Endless.toUnlimited[A])    .to[ Unlimited[A] |*| S ]

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

    implicit def comonoidUnlimited[A]: Comonoid[Unlimited[A]] =
      new Comonoid[Unlimited[A]] {
        def counit : Unlimited[A] -⚬ One                             = Unlimited.discard
        def split  : Unlimited[A] -⚬ (Unlimited[A] |*| Unlimited[A]) = Unlimited.split
      }

    implicit val comonadUnlimited: Comonad[Unlimited] =
      new Comonad[Unlimited] {
        def extract[A]   : Unlimited[A] -⚬ A                       = Unlimited.single
        def duplicate[A] : Unlimited[A] -⚬ Unlimited[Unlimited[A]] = Unlimited.duplicate
      }

    /** Signals when the choice is made between [[discard]], [[single]] and [[split]]. */
    implicit def signalingUnlimited[A]: Signaling.Negative[Unlimited[A]] = {
      val notifyFst: (Pong |*| Unlimited[A]) -⚬ Unlimited[A] =
        par(id, unpack) > notifyChoiceAndRight > pack[UnlimitedF[A, *]]

      Signaling.Negative.from(notifyFst)
    }

    implicit def deferrableUnlimited[A]: Deferrable.Negative[Unlimited[A]] =
      new Deferrable.Negative[Unlimited[A]] {
        override def awaitPongFst: Unlimited[A] -⚬ (Pong |*| Unlimited[A]) =
          unpack > delayChoiceUntilPong > snd(pack[UnlimitedF[A, *]])
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

    def duplicate[A]: PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] = rec { self =>
      create(
        case0 = neglect,
        case1 = id,
        caseN = split > par(self, self)
      )
    }

    implicit def pComonoidPUnlimited[A]: PComonoid[PUnlimited[A]] =
      new PComonoid[PUnlimited[A]] {
        def counit : PUnlimited[A] -⚬ Done                              = PUnlimited.neglect
        def split  : PUnlimited[A] -⚬ (PUnlimited[A] |*| PUnlimited[A]) = PUnlimited.split
      }

    implicit val comonadPUnlimited: Comonad[PUnlimited] =
      new Comonad[PUnlimited] {
        def extract[A]   : PUnlimited[A] -⚬ A                         = PUnlimited.single
        def duplicate[A] : PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] = PUnlimited.duplicate
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

    implicit val nAffineNeed: NAffine[Need] =
      from(id)

    implicit def nAffinePair[A, B](implicit A: NAffine[A], B: NAffine[B]): NAffine[A |*| B] =
      from(par(A.deflate, B.deflate) > forkNeed)
  }

  trait Affine[A] {
    def discard: A -⚬ One
  }

  object Affine {
    def from[A](f: A -⚬ One): Affine[A] =
      new Affine[A] {
        override def discard: A -⚬ One =
          f
      }

    implicit def fromNAffine[A](implicit A: NAffine[A]): Affine[A] =
      from(A.deflate > need)

    implicit def affinePair[A, B](implicit A: Affine[A], B: Affine[B]): Affine[A |*| B] =
      from(parToOne(A.discard, B.discard))
  }

  trait PAffine[A] {
    def neglect: A -⚬ Done
  }

  object PAffine {
    def from[A](f: A -⚬ Done): PAffine[A] =
      new PAffine[A] {
        override def neglect: A -⚬ Done =
          f
      }

    implicit def fromAffine[A](implicit A: Affine[A]): PAffine[A] =
      from(A.discard > done)

    implicit val pAffineDone: PAffine[Done] =
      from(id)

    implicit def pAffinePair[A, B](implicit A: PAffine[A], B: PAffine[B]): PAffine[A |*| B] =
      from(par(A.neglect, B.neglect) > join)
  }

  trait Semigroup[A] {
    def combine: (A |*| A) -⚬ A

    def law_associativity: Equal[ ((A |*| A) |*| A) -⚬ A ] =
      Equal(
        par(combine, id[A]) > combine,
        |*|.assocLR > par(id[A], combine) > combine,
      )
  }

  object Semigroup {
    implicit val semigroupDone: Semigroup[Done] =
      new Semigroup[Done] {
        override def combine: (Done |*| Done) -⚬ Done = join
      }

    implicit val semigroupNeed: Semigroup[Need] =
      new Semigroup[Need] {
        override def combine: (Need |*| Need) -⚬ Need = forkNeed
      }
  }

  trait Cosemigroup[A] {
    def split: A -⚬ (A |*| A)

    def law_coAssociativity: Equal[ A -⚬ ((A |*| A) |*| A) ] =
      Equal(
        split > par(split, id[A]),
        split > par(id[A], split) > |*|.assocRL,
      )
  }

  object Cosemigroup {
    implicit val cosemigroupDone: Cosemigroup[Done] =
      new Cosemigroup[Done] {
        override def split: Done -⚬ (Done |*| Done) = fork
      }

    implicit val cosemigroupNeed: Cosemigroup[Need] =
      new Cosemigroup[Need] {
        override def split: Need -⚬ (Need |*| Need) = joinNeed
      }
  }

  trait Monoid[A] extends Semigroup[A] {
    def unit: One -⚬ A

    def law_leftUnit: Equal[ (One |*| A) -⚬ A ] =
      Equal(
        par(unit, id[A]) > combine,
        elimFst,
      )

    def law_rightUnit: Equal[ (A |*| One) -⚬ A ] =
      Equal(
        par(id[A], unit) > combine,
        elimSnd,
      )
  }

  object Monoid {
    implicit val monoidOne: Monoid[One] =
      new Monoid[One] {
        override def unit   :           One -⚬ One = id
        override def combine: (One |*| One) -⚬ One = elimSnd[One]
      }

    implicit val monoidDone: Monoid[Done] =
      new Monoid[Done] {
        override def unit   :             One -⚬ Done = done
        override def combine: (Done |*| Done) -⚬ Done = join
      }
  }

  trait Comonoid[A] extends Cosemigroup[A] with Affine[A] {
    def counit: A -⚬ One

    override def discard: A -⚬ One =
      counit

    def law_leftCounit: Equal[ A -⚬ (One |*| A) ] =
      Equal(
        split > par(counit, id[A]),
        introFst,
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| One) ] =
      Equal(
        split > par(id[A], counit),
        introSnd,
      )
  }

  object Comonoid {
    implicit val comonoidOne: Comonoid[One] =
      new Comonoid[One] {
        override def counit: One -⚬ One = id[One]
        override def split: One -⚬ (One |*| One) = introSnd[One]
      }

    implicit val comonoidNeed: Comonoid[Need] =
      new Comonoid[Need] {
        override def split  : Need -⚬ (Need |*| Need) = joinNeed
        override def counit : Need -⚬ One             = need
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
        par(done > unit, id[A]) > combine,
        elimFst,
      )

    def law_rightUnit: Equal[ (A |*| One) -⚬ A ] =
      Equal(
        par(id[A], done > unit) > combine,
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
        split > par(counit > need, id[A]),
        introFst,
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| One) ] =
      Equal(
        split > par(id[A], counit > need),
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
        par(regressInfinitely > unit, id[A]) > combine,
        id[LTerminus |*| A].elimFst(regressInfinitely > need),
      )

    def law_rightUnit: Equal[ (A |*| LTerminus) -⚬ A ] =
      Equal(
        par(id[A], regressInfinitely > unit) > combine,
        id[A |*| LTerminus].elimSnd(regressInfinitely > need),
      )
  }

  object NMonoid {
    implicit val nMonoidNeed: NMonoid[Need] =
      new NMonoid[Need] {
        override def combine : (Need |*| Need) -⚬ Need = forkNeed
        override def unit    :            Need -⚬ Need = id
      }
  }

  /** A weaker version of [[Comonoid]] whose [[counit]] cannot discard the input completely, but can reduce it to
    * a signal traveling in the '''P'''ositive direction ([[Done]]) that eventually needs to be awaited.
    *
    * The dual of [[NMonoid]].
    */
  trait PComonoid[A] extends Cosemigroup[A] with PAffine[A] {
    def counit: A -⚬ Done

    override def neglect: A -⚬ Done =
      counit

    def law_leftCounit: Equal[ A -⚬ (RTerminus |*| A) ] =
      Equal(
        split > par(counit > delayIndefinitely, id[A]),
        id[A].introFst(done > delayIndefinitely),
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| RTerminus) ] =
      Equal(
        split > par(id[A], counit > delayIndefinitely),
        id[A].introSnd(done > delayIndefinitely),
      )
  }

  object PComonoid {
    implicit val pComonoidDone: PComonoid[Done] =
      new PComonoid[Done] {
        override def split  : Done -⚬ (Done |*| Done) = fork
        override def counit : Done -⚬ Done            = id
      }
  }

  trait Monad[F[_]] {
    def pure[A]    :       A -⚬ F[A]
    def flatten[A] : F[F[A]] -⚬ F[A]
  }

  trait Comonad[F[_]] {
    def extract[A]   : F[A] -⚬ A
    def duplicate[A] : F[A] -⚬ F[F[A]]
  }

  def getFst[A, B](implicit A: Cosemigroup[A]): (A |*| B) -⚬ (A |*| (A |*| B)) =
    id                             [     A     |*| B  ]
      .>.fst(A.split)           .to[ (A |*| A) |*| B  ]
      .assocLR                  .to[  A |*| (A |*| B) ]

  def getSnd[A, B](implicit B: Cosemigroup[B]): (A |*| B) -⚬ (B |*| (A |*| B)) =
    id                             [  A |*|     B     ]
      .>.snd(B.split)           .to[  A |*| (B |*| B) ]
      .assocRL                  .to[ (A |*| B) |*| B  ]
      .swap                     .to[  B |*| (A |*| B) ]

  def discardFst[A, B](implicit A: Comonoid[A]): (A |*| B) -⚬ B =
    id                             [  A  |*| B ]
      .elimFst(A.counit)        .to[         B ]

  def discardSnd[A, B](implicit B: Comonoid[B]): (A |*| B) -⚬ A =
    id                             [ A |*|  B  ]
      .elimSnd(B.counit)        .to[ A         ]

  private type LListF[T, X] = One |+| (T |*| X)
  opaque type LList[T] = Rec[LListF[T, *]]

  object LList {
    private def unpack[T]: LList[T] -⚬ LListF[T, LList[T]] = dsl.unpack
    private def pack[T]  : LListF[T, LList[T]] -⚬ LList[T] = dsl.pack

    def nil[T]: One -⚬ LList[T] =
      id[One]
        .injectL[T |*| LList[T]]
        .pack

    def cons[T]: (T |*| LList[T]) -⚬ LList[T] =
      id[T |*| LList[T]]
        .injectR[One]
        .pack

    def singleton[T]: T -⚬ LList[T] =
      introSnd(nil[T]) > cons[T]

    def uncons[T]: LList[T] -⚬ Maybe[T |*| LList[T]] =
      unpack

    /** Signals when it is decided whether the list is empty (nil) or has an element (cons). */
    implicit def signalingLList[T]: Signaling.Positive[LList[T]] =
      Signaling.Positive.from(unpack > notifyEither > par(id, pack))

    def fromList0[S, T](fs: List[S -⚬ T])(using S: Cosemigroup[S]): S -⚬ (S |*| LList[T]) = {
      @tailrec def go(rfs: List[S -⚬ T], acc: S -⚬ (S |*| LList[T])): S -⚬ (S |*| LList[T]) =
        rfs match {
          case head :: tail => go(tail, S.split > par(id, acc > par(head, id) > cons))
          case Nil => acc
        }

      go(fs.reverse, id[S] > introSnd(nil[T]))
    }

    def fromList[S, T](fs: List[S -⚬ T])(using S: Comonoid[S]): S -⚬ LList[T] =
      fromList0(fs) > discardFst

    def fromListU[S, T](fs: List[S -⚬ T]): Unlimited[S] -⚬ LList[T] = {
      import Unlimited.comonoidUnlimited

      fromList(fs map (Unlimited.single > _))
    }

    def of[S, T](fs: (S -⚬ T)*)(using S: Comonoid[S]): S -⚬ LList[T] =
      fromList(fs.toList)

    def switch[T, R](
      caseNil: One -⚬ R,
      caseCons: (T |*| LList[T]) -⚬ R,
    ): LList[T] -⚬ R =
      uncons[T].either(caseNil, caseCons)

    def switchWithL[A, T, R](
      caseNil: A -⚬ R,
      caseCons: (A |*| (T |*| LList[T])) -⚬ R,
    ): (A |*| LList[T]) -⚬ R =
      par(id, uncons[T]) > distributeL > either(elimSnd > caseNil, caseCons)

    def switchWithR[A, T, R](
      caseNil: A -⚬ R,
      caseCons: ((T |*| LList[T]) |*| A) -⚬ R,
    ): (LList[T] |*| A) -⚬ R =
      swap > switchWithL(caseNil, swap > caseCons)

    def map[T, U](f: T -⚬ U): LList[T] -⚬ LList[U] =
      rec { self =>
        switch(nil[U], par(f, self) > cons)
      }

    def mapS[S, T, U](f: (S |*| T) -⚬ (S |*| U)): (S |*| LList[T]) -⚬ (S |*| LList[U]) = rec { self =>
      switchWithL(
        caseNil = id[S] > introSnd(nil[U]),
        caseCons = assocRL > fst(f > swap) > assocLR > snd(self) > XI > snd(cons[U]),
      )
    }

    def mapSAppend[S, T, U](f: (S |*| T) -⚬ (S |*| U), tail: S -⚬ LList[U]): (S |*| LList[T]) -⚬ LList[U] = rec { self =>
      switchWithL(
        caseNil = tail,
        caseCons = assocRL > fst(f > swap) > assocLR > snd(self)> cons[U],
      )
    }

    def actOn[S, A](act: (S |*| A) -⚬ S): (S |*| LList[A]) -⚬ S = rec { self =>
      switchWithL(
        caseNil  = id[S],
        caseCons = assocRL > par(act, id) > self
      )
    }

    def foldMap0[T, U](f: T -⚬ U)(implicit U: Semigroup[U]): LList[T] -⚬ Maybe[U] =
      switch(
        caseNil  = Maybe.empty[U],
        caseCons = par(f, id) > actOn[U, T](par(id, f) > U.combine) > Maybe.just[U],
      )

    def foldMap[T, U](f: T -⚬ U)(implicit U: Monoid[U]): LList[T] -⚬ U =
      rec { self =>
        switch(U.unit, par(f, self) > U.combine)
      }

    def fold0[T](implicit T: Semigroup[T]): LList[T] -⚬ Maybe[T] =
      foldMap0(id[T])

    def fold[T](implicit T: Monoid[T]): LList[T] -⚬ T =
      foldMap(id[T])

    def foldL[S, T](f: (S |*| T) -⚬ S): (S |*| LList[T]) -⚬ S = rec { self =>
      switchWithL(
        caseNil = id[S],
        caseCons = assocRL > fst(f) > self
      )
    }

    def concat[T]: (LList[T] |*| LList[T]) -⚬ LList[T] = rec { self =>
      switchWithR(
        caseNil  = id[LList[T]],
        caseCons = assocLR > par(id, self) > cons,
      )
    }

    def consMaybe[T]: (Maybe[T] |*| LList[T]) -⚬ LList[T] =
      id[Maybe[T] |*| LList[T]]             .to[ (One |+|                T) |*| LList[T] ]
        .distributeR                        .to[ (One |*| LList[T]) |+| (T |*| LList[T]) ]
        .>(either(elimFst, cons))           .to[                 LList[T]                ]

    def collect[T, U](f: T -⚬ Maybe[U]): LList[T] -⚬ LList[U] =
      rec { self =>
        switch(nil[U], par(f, self) > consMaybe)
      }

    def transform[T, A, U](f: (A |*| T) -⚬ U)(implicit A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
      rec { self =>
        val caseNil: A -⚬ LList[U] =
          A.discard > nil[U]
        val caseCons: (A |*| (T |*| LList[T])) -⚬ LList[U] =
          par(A.split, id) > IXI > par(f, self) > cons[U]
        switchWithL(caseNil, caseCons)
      }

    def transformCollect[T, A, U](f: (A |*| T) -⚬ Maybe[U])(implicit A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
      rec { self =>
        val caseNil: A -⚬ LList[U] =
          A.discard > nil[U]
        val caseCons: (A |*| (T |*| LList[T])) -⚬ LList[U] =
          par(A.split, id) > IXI > par(f, self) > consMaybe[U]
        switchWithL(caseNil, caseCons)
      }

    def unzip[A, B]: LList[A |*| B] -⚬ (LList[A] |*| LList[B]) = rec { self =>
      val caseNil: One -⚬ (LList[A] |*| LList[B]) =
        parFromOne(nil[A], nil[B])

      val caseCons: ((A |*| B) |*| LList[A |*| B]) -⚬ (LList[A] |*| LList[B]) =
        par(id, self) > IXI > par(cons, cons)

      switch(caseNil, caseCons)
    }

    def splitEvenOdd[A]: LList[A] -⚬ (LList[A] |*| LList[A]) = rec { self =>
      val caseCons: (A |*| LList[A]) -⚬ (LList[A] |*| LList[A]) =
        switchWithL(
          caseNil  = singleton[A] > introSnd(nil[A]),
          caseCons = |*|.assocRL > par(id, self) > IXI > par(cons, cons),
        )

      switch(
        caseNil  = parFromOne(nil[A], nil[A]),
        caseCons = caseCons,
      )
    }

    private def waveL[A, S, B](
      init: A -⚬ S,
      f: (S |*| A) -⚬ (B |*| S),
      last: S -⚬ B,
    ): LList[A] -⚬ LList[B] =
      switch(
        caseNil  = nil[B],
        caseCons = fst(init) > mapSAppend(f > swap, last > singleton),
      )

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
        IXI.>.snd(swap)

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
    def merge[T]: (LList[T] |*| LList[T]) -⚬ LList[T] = rec { self =>
      race(
        caseFstWins = switchWithR(
          caseNil = id[LList[T]],
          caseCons = assocLR > par(id, self) > cons,
        ),
        caseSndWins = switchWithL(
          caseNil = id[LList[T]],
          caseCons = XI > par(id, self) > cons,
        ),
      )
    }

    /** Inserts an element to a list as soon as the element signals.
     *  If _m_ elements of the input list become available before the new element signals,
     *  the new element will appear as the _(m+1)_-th element in the output list.
     *  Note: The _m_ elements from the input list are not awaited to signal;
     *  their timely appearence in the input list is sufficient for them to come before
     *  the inserted element.
     */
    def insertBySignal[T: Signaling.Positive]: (T |*| LList[T]) -⚬ LList[T] =
      par(singletonOnSignal[T], id) > merge[T]

    /** Make the elements of the input list available in the output list in the order in which they signal. */
    def sortBySignal[T: Signaling.Positive]: LList[T] -⚬ LList[T] = rec { self =>
      // XXX O(n^2) complexity: if the element at the end of the list signals first, it will take O(n) steps for it
      // to bubble to the front. Could be improved to O(log(n)) steps to bubble any element and O(n*log(n)) total
      // complexity by using a heap data structure.
      switch(
        caseNil = nil[T],
        caseCons = par(id[T], self) > insertBySignal[T],
      )
    }

    implicit def monoidLList[A]: Monoid[LList[A]] =
      new Monoid[LList[A]] {
        def unit    :                     One -⚬ LList[A] = nil
        def combine : (LList[A] |*| LList[A]) -⚬ LList[A] = concat
      }
  }

  /** Non-empty list, i.e. a list with at least one element. */
  opaque type LList1[T] = T |*| LList[T]
  object LList1 {
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

    def from[S, T](fs: ::[S -⚬ T])(using S: Cosemigroup[S]): S -⚬ LList1[T] =
      from(fs.head, fs.tail)

    def of[S, T](head: S -⚬ T, tail: (S -⚬ T)*)(using S: Cosemigroup[S]): S -⚬ LList1[T] =
      from(head, tail.toList)

    def map[T, U](f: T -⚬ U): LList1[T] -⚬ LList1[U] =
      par(f, LList.map(f))

    def mapS[S, T, U](f: (S |*| T) -⚬ (S |*| U)): (S |*| LList1[T]) -⚬ (S |*| LList1[U]) =
      assocRL > fst(f > swap) > assocLR > snd(LList.mapS(f)) > XI

    def mapSAppend[S, T, U](f: (S |*| T) -⚬ (S |*| U), tail: S -⚬ LList[U]): (S |*| LList1[T]) -⚬ LList1[U] =
      assocRL > fst(f > swap) > assocLR > snd(LList.mapSAppend(f, tail))

    def foldMap[T, U](f: T -⚬ U)(using U: Semigroup[U]): LList1[T] -⚬ U =
      par(f, id) > LList.actOn[U, T](par(id, f) > U.combine)

    def fold[T](using T: Semigroup[T]): LList1[T] -⚬ T =
      LList.actOn[T, T](T.combine)

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
    def insertBySignal[T: Signaling.Positive]: (T |*| LList[T]) -⚬ LList1[T] = {
      import LList.signalingLList

      race(
        caseFstWins = cons[T],
        caseSndWins = LList.switchWithL(
          caseNil = singleton[T],
          caseCons = XI > par(id, LList.insertBySignal[T]),
        ),
      )
    }
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

    def close[A]: Endless[A] -⚬ One =
      unpack > chooseL

    def pull[A]: Endless[A] -⚬ (A |*| Endless[A]) =
      unpack > chooseR

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

    def unfold[S, A](f: S -⚬ (A |*| S)): S -⚬ (Endless[A] |*| S) = rec { self =>
      createWith[S, A, S](
        onClose = id[S],
        onPull = f > par(id, self) > assocRL,
      )
    }

    /** Signals when the consumer makes a choice, i.e. [[close]] or [[pull]]. */
    implicit def signalingEndless[A]: Signaling.Negative[Endless[A]] =
      Signaling.Negative.from(par(id, unpack) > notifyChoice > pack)

    def split[A]: Endless[A] -⚬ (Endless[A] |*| Endless[A]) = rec { self =>
      val onFstAction: Endless[A] -⚬ (Endless[A] |*| Endless[A]) = {
        val onClose: Endless[A] -⚬ (One |*| Endless[A]) =
          introFst
        val onPull: Endless[A] -⚬ ((A |*| Endless[A]) |*| Endless[A]) =
          pull > par(id, self) > assocRL

        id                                   [                    Endless[A]                 |*| Endless[A]  ]
          .<.fst(pack)                  .from[ (One                 |&|  (A |*| Endless[A])) |*| Endless[A]  ]
          .<(coDistributeR)             .from[ (One |*| Endless[A]) |&| ((A |*| Endless[A])  |*| Endless[A]) ]
          .<(choice(onClose, onPull))   .from[                   Endless[A]                                  ]
      }

      val onSndAction: Endless[A] -⚬ (Endless[A] |*| Endless[A]) =
        onFstAction > swap

      select(
        caseFstWins = onFstAction,
        caseSndWins = onSndAction,
      )
    }

    implicit def comonoidEndless[A]: Comonoid[Endless[A]] =
      new Comonoid[Endless[A]] {
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
  }

  /** Present a non-empty list of resources `A` as an unlimited supply of "borrowed" resources `A ⊗ Ā`,
    * where `Ā` is the dual of `A`. A borrowed resource `A ⊗ Ā` must be "returned" by "annihilating"
    * `A` and its dual `Ā`, namely via an inversion on the right `A ⊗ Ā -⚬ One`.
    * A returned resource will become available for further use when it signals readiness using the
    * [[Signaling.Positive]] instance.
    *
    * When all accesses to the pooled resources (obtained via the `Unlimited[A |*| Ā]` in the first
    * out-port) are closed, the resources are returned in the second out-port.
    */
  def pool[A: Signaling.Positive, Ā](
    lInvert: One -⚬ (Ā |*| A),
  ): LList1[A] -⚬ (Unlimited[A |*| Ā] |*| LList1[A]) = rec { self =>
    val borrow: LList1[A] -⚬ ((A |*| Ā) |*| LList1[A]) =
      id                                         [     LList1[A]                   ]
        .>(LList1.uncons)                     .to[   A |*|               LList[A]  ]
        .>.fst(introSnd(lInvert) > assocRL)   .to[ ((A |*| Ā) |*| A) |*| LList[A]  ]
        .>(assocLR)                           .to[  (A |*| Ā) |*| (A |*| LList[A]) ]
        .>.snd(LList1.insertBySignal)         .to[  (A |*| Ā) |*|    LList1[A]     ]

    Unlimited.unfold(borrow)
  }
}
