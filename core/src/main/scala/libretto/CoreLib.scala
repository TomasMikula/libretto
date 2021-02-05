package libretto

import libretto.unapply._
import scala.annotation.tailrec

object CoreLib {
  def apply(dsl: CoreDSL): CoreLib[dsl.type] =
    new CoreLib(dsl)
}

class CoreLib[DSL <: CoreDSL](val dsl: DSL) { lib =>
  import dsl._

  /** Evidence that `A` flowing in one direction is equivalent to to `B` flowing in the opposite direction.
    * It must hold that
    * {{{
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
    * }}}
    */
  trait Dual[A, B] {
    /** Reverses the input that flows along the `-⚬` arrow (say it is the `A` input) to its dual (`B`) flowing
      * against the direction of the arrow.
      *
      * {{{
      *   ┏━━━━━━━┓
      *   ┞─┐   r ┃
      *   ╎A│─┐ I ┃
      *   ┟─┘ ┆ n ┃
      *   ┃   ┆ v ┃
      *   ┞─┐ ┆ e ┃
      *   ╎B│←┘ r ┃
      *   ┟─┘   t ┃
      *   ┗━━━━━━━┛
      * }}}
      */
    val rInvert: (A |*| B) -⚬ One

    /** Reverses the output that flows against the `-⚬` arrow (say it is the `B` output) to its dual (`A`) flowing
      * in the direction of the arrow.
      *
      * {{{
      *   ┏━━━━━┓
      *   ┃ l   ┞─┐
      *   ┃ I ┌─╎B│
      *   ┃ n ┆ ┟─┘
      *   ┃ v ┆ ┃
      *   ┃ e ┆ ┞─┐
      *   ┃ r └→╎A│
      *   ┃ t   ┟─┘
      *   ┗━━━━━┛
      * }}}
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
    def ⚬[G[_]](that: Functor[G]): Functor[λ[x => F[G[x]]]] = new Functor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[A]] -⚬ F[G[B]] = self.lift(that.lift(f))
    }

    /** Composition with a contravariant functor. Results in a contravariant functor. */
    def ⚬[G[_]](that: ContraFunctor[G]): ContraFunctor[λ[x => F[G[x]]]] = new ContraFunctor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[B]] -⚬ F[G[A]] = self.lift(that.lift(f))
    }
  }

  /** Witnesses that `F` is a contravariant endofunctor on the category `-⚬`. */
  trait ContraFunctor[F[_]] { self =>
    def lift[A, B](f: A -⚬ B): F[B] -⚬ F[A]

    /** Composition with a covariant functor. Results in a contravariant functor. */
    def ⚬[G[_]](that: Functor[G]): ContraFunctor[λ[x => F[G[x]]]] = new ContraFunctor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[B]] -⚬ F[G[A]] = self.lift(that.lift(f))
    }

    /** Composition with another contravariant functor. Results in a covariant functor. */
    def ⚬[G[_]](that: ContraFunctor[G]): Functor[λ[x => F[G[x]]]] = new Functor[λ[x => F[G[x]]]] {
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

    def ⚬[G[_]](that: Functor[G]): Externalizer[[x] =>> F[G[x]]] =
      new Externalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[A]] => F[G[B]] =
          self.lift(that.lift(f))
      }

    def ⚬[G[_]](that: ContraFunctor[G]): ContraExternalizer[[x] =>> F[G[x]]] =
      new ContraExternalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[B]] => F[G[A]] =
          self.lift(that.lift(f))
      }

    def ⚬[G[_, _]](that: Bifunctor[G]): BiExternalizer[[x, y] =>> F[G[x, y]]] =
      new BiExternalizer[[x, y] =>> F[G[x, y]]] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): F[G[A, C]] => F[G[B, D]] =
          self.lift(that.lift(f, g))
      }
  }

  object Externalizer {
    implicit def outportInstance[A]: Externalizer[[x] =>> A -⚬ x] =
      new Externalizer[[x] =>> A -⚬ x] {
        def lift[B, C](f: B -⚬ C): (A -⚬ B) => (A -⚬ C) =
          _ >>> f
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

    def ⚬[G[_]](that: Functor[G]): ContraExternalizer[[x] =>> F[G[x]]] =
      new ContraExternalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[B]] => F[G[A]] =
          self.lift(that.lift(f))
      }

    def ⚬[G[_]](that: ContraFunctor[G]): Externalizer[[x] =>> F[G[x]]] =
      new Externalizer[[x] =>> F[G[x]]] {
        def lift[A, B](f: A -⚬ B): F[G[A]] => F[G[B]] =
          self.lift(that.lift(f))
      }
  }

  object ContraExternalizer {
    implicit def inportInstance[C]: ContraExternalizer[[x] =>> x -⚬ C] =
      new ContraExternalizer[[x] =>> x -⚬ C] {
        def lift[A, B](f: A -⚬ B): (B -⚬ C) => (A -⚬ C) =
          f >>> _
      }
  }

  /** A type alias expressing the ''intent'' that `A` is delayed (in some sense) until a signal ([[Need]]) is received.
    * Equivalent to `Done =⚬ A`, but the formulation as `Need |*| A` does not rely on the more powerful concept
    * of ''function types'' (internal hom objects), i.e. does not require [[ClosedDSL]].
    */
  type Delayed[A] = Need |*| A
  object Delayed {
    def triggerBy[A]: (Done |*| Delayed[A]) -⚬ A =
      |*|.assocRL >>> elimFst(rInvertSignal)

    def force[A]: Delayed[A] -⚬ A =
      elimFst(need)

    /** Signals when it is triggered, awaiting delays the trigger. */
    def signalingJunction[A]: SignalingJunction.Negative[Delayed[A]] =
      SignalingJunction.Negative.byFst
  }

  object Junction {
    /** Represents ''a'' way how `A` can await (join) a positive (i.e. [[Done]]) signal. */
    trait Positive[A] {
      def awaitPosFst: (Done |*| A) -⚬ A

      def awaitPosSnd: (A |*| Done) -⚬ A =
        swap >>> awaitPosFst

      /** Alias for [[awaitPosFst]]. */
      def awaitPos: (Done |*| A) -⚬ A =
        awaitPosFst

      def law_awaitIdentity: Equal[(One |*| A) -⚬ A] =
        Equal(
          par(done, id) >>> awaitPosFst,
          elimFst,
        )

      def law_AwaitComposition: Equal[(Done |*| (Done |*| A)) -⚬ A] =
        Equal(
          par(id, awaitPosFst) >>> awaitPosFst,
          |*|.assocRL >>> par(join, id) >>> awaitPosFst,
        )
    }

    /** Represents ''a'' way how `A` can await (join) a negative (i.e. [[Need]]) signal. */
    trait Negative[A] {
      def awaitNegFst: A -⚬ (Need |*| A)

      def awaitNegSnd: A -⚬ (A |*| Need) =
        awaitNegFst >>> swap

      /** Alias for [[awaitNegFst]]. */
      def awaitNeg: A -⚬ (Need |*| A) =
        awaitNegFst

      def law_awaitIdentity: Equal[A -⚬ (One |*| A)] =
        Equal(
          awaitNegFst >>> par(need, id),
          introFst,
        )

      def law_awaitComposition: Equal[A -⚬ (Need |*| (Need |*| A))] =
        Equal(
          awaitNegFst >>> par(id, awaitNegFst),
          awaitNegFst >>> par(joinNeed, id) >>> |*|.assocLR,
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

      def delegateToEither[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |+| B] =
        from( distributeLR[Done, A, B].bimap(A.awaitPosFst, B.awaitPosFst) )

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

      def delegateToEither[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        from( id[A |+| B].bimap(A.awaitNegFst, B.awaitNegFst).factorL )

      def delayEither[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        from( id[A |+| B].bimap(A.awaitNegFst, B.awaitNegFst) >>> delayEitherUntilNeed )

      def delegateToChosen[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        from( id[A |&| B].bimap(A.awaitNegFst, B.awaitNegFst).coDistributeL )

      def delayChoice[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        from( id[A |&| B].bimap(A.awaitNegFst, B.awaitNegFst) >>> delayChoiceUntilNeed )

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
    /** Represents ''a'' way how `A` can produce a positive (i.e. [[Done]]) signal. */
    trait Positive[A] {
      def signalPosFst: A -⚬ (Done |*| A)

      def signalPosSnd: A -⚬ (A |*| Done) =
        signalPosFst >>> swap

      /** Alias for [[signalPosFst]]. */
      def signalPos: A -⚬ (Done |*| A) =
        signalPosFst

      def law_signalIdentity: Equal[A -⚬ (RTerminus |*| A)] =
        Equal(
          signalPosFst >>> par(delayIndefinitely, id),
          id[A] >>> introFst(done >>> delayIndefinitely),
        )

      def law_awaitComposition: Equal[A -⚬ (Done |*| (Done |*| A))] =
        Equal(
          signalPosFst >>> par(id, signalPosFst),
          signalPosFst >>> par(fork, id) >>> |*|.assocLR,
        )
    }

    /** Represents ''a'' way how `A` can produce a negative (i.e. [[Need]]) signal. */
    trait Negative[A] {
      def signalNegFst: (Need |*| A) -⚬ A

      def signalNegSnd: (A |*| Need) -⚬ A =
        swap >>> signalNegFst

      /** Alias for [[signalNegFst]]. */
      def signalNeg: (Need |*| A) -⚬ A =
        signalNegFst

      def law_signalIdentity: Equal[(LTerminus |*| A) -⚬ A] =
        Equal(
          par(regressInfinitely, id) >>> signalNegFst,
          id[LTerminus |*| A] >>> elimFst(regressInfinitely >>> need),
        )

      def law_signalComposition: Equal[(Need |*| (Need |*| A)) -⚬ A] =
        Equal(
          par(id, signalNegFst) >>> signalNegFst,
          |*|.assocRL >>> par(forkNeed, id) >>> signalNegFst,
        )
    }

    object Positive {
      def from[A](signal: A -⚬ (Done |*| A)): Signaling.Positive[A] =
        new Signaling.Positive[A] {
          override def signalPosFst: A -⚬ (Done |*| A) =
            signal
        }

      implicit def signalingDone: Signaling.Positive[Done] =
        from(fork)

      def byFst[A, B](implicit A: Signaling.Positive[A]): Signaling.Positive[A |*| B] =
        from(par(A.signalPosFst, id[B]).assocLR)

      def bySnd[A, B](implicit B: Signaling.Positive[B]): Signaling.Positive[A |*| B] =
        from(par(id[A], B.signalPosFst) > XI)

      /** Signals when it is decided which side of the [[|+|]] is present. */
      def either[A, B]: Signaling.Positive[A |+| B] =
        from(dsl.signalEither[A, B])

      def rec[F[_]](implicit F: Positive[F[Rec[F]]]): Positive[Rec[F]] =
        from(unpack > F.signalPosFst > par(id, pack))

      def rec[F[_]](implicit F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        rec(F[Rec[F]])

      def rec[F[_]](f: Positive[Rec[F]] => Positive[F[Rec[F]]]): Positive[Rec[F]] =
        from(dsl.rec(g => unpack > f(from(g)).signalPosFst > par(id, pack)))
    }

    object Negative {
      def from[A](signal: (Need |*| A) -⚬ A): Signaling.Negative[A] =
        new Signaling.Negative[A] {
          override def signalNegFst: (Need |*| A) -⚬ A =
            signal
        }

      implicit def signalingNeed: Signaling.Negative[Need] =
        from(forkNeed)

      def byFst[A, B](implicit A: Signaling.Negative[A]): Signaling.Negative[A |*| B] =
        from(|*|.assocRL.>.fst(A.signalNegFst))

      def bySnd[A, B](implicit B: Signaling.Negative[B]): Signaling.Negative[A |*| B] =
        from(XI > par(id[A], B.signalNegFst))

      /** Signals when the choice is made between [[A]] and [[B]]. */
      def choice[A, B]: Signaling.Negative[A |&| B] =
        from(dsl.signalChoice[A, B])

      def rec[F[_]](implicit F: Negative[F[Rec[F]]]): Negative[Rec[F]] =
        from(par(id, unpack) > F.signalNegFst > pack)

      def rec[F[_]](implicit F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        rec(F[Rec[F]])

      def rec[F[_]](f: Negative[Rec[F]] => Negative[F[Rec[F]]]): Negative[Rec[F]] =
        from(dsl.rec(g => par(id, unpack) > f(from(g)).signalNegFst > pack))
    }

    /** [[Signaling.Positive]] can be made to produce a negative (i.e. [[Need]]) signal,
      * by inverting the produced signal (via [[rInvertSignal]]).
      */
    def invert[A](A: Positive[A]): Negative[A] =
      new Negative[A] {
        override def signalNegFst: (Need |*| A) -⚬ A =
          id                                     [  Need |*|            A  ]
            .>.snd(A.signalPosFst)            .to[  Need |*| (Done  |*| A) ]
            .assocRL                          .to[ (Need |*|  Done) |*| A  ]
            .elimFst(swap >>> rInvertSignal)  .to[                      A  ]
      }

    /** [[Signaling.Negative]] can be made to produce a positive (i.e. [[Done]]) signal,
      * by inverting the produced signal (via [[lInvertSignal]]).
      */
    def invert[A](A: Negative[A]): Positive[A] =
      new Positive[A] {
        override def signalPosFst: A -⚬ (Done |*| A) =
          id                                     [                      A  ]
            .introFst(lInvertSignal >>> swap) .to[ (Done |*|  Need) |*| A  ]
            .assocLR                          .to[  Done |*| (Need  |*| A) ]
            .>.snd(A.signalNegFst)            .to[  Done |*|            A  ]
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
          signalPos >>> awaitPos,
          id[A],
        )

      /** Expresses that awaiting a signal and then signaling does not speed up the original signal, i.e. that
        * the point of signaling in [[A]] is causally dependent on the point of awaiting in [[A]].
        */
      def law_positiveAwaitThenSignal: Equal[(Done |*| A) -⚬ (Done |*| A)] =
        Equal(
          awaitPos >>> signalPos,
          par(fork, id) >>> |*|.assocLR >>> par(id, awaitPos >>> signalPos) >>> |*|.assocRL >>> par(join, id),
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
          awaitNeg >>> signalNeg,
          id[A],
        )

      /** Expresses that awaiting a signal and then signaling does not speed up the original signal, i.e. that
        * the point of signaling in [[A]] is causally dependent on the point of awaiting in [[A]].
        */
      def law_negativeSignalThenAwait: Equal[(Need |*| A) -⚬ (Need |*| A)] =
        Equal(
          signalNeg >>> awaitNeg,
          par(joinNeed, id) >>> |*|.assocLR >>> par(id, signalNeg >>> awaitNeg) >>> |*|.assocRL >>> par(forkNeed, id),
        )
    }

    object Positive {
      def from[A](s: Signaling.Positive[A], j: Junction.Positive[A]): SignalingJunction.Positive[A] =
        new SignalingJunction.Positive[A] {
          override def signalPosFst: A -⚬ (Done |*| A) = s.signalPosFst
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
          override def signalNegFst: (Need |*| A) -⚬ A = s.signalNegFst
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

  def delayUsing[A](f: Done -⚬ Done)(implicit A: SignalingJunction.Positive[A]): A -⚬ A =
    A.delayUsing(f)

  def delayUsing[A](f: Need -⚬ Need)(implicit A: SignalingJunction.Negative[A]): A -⚬ A =
    A.delayUsing(f)

  def race[A, B](implicit
    A: SignalingJunction.Positive[A],
    B: SignalingJunction.Positive[B],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    id                                               [                   A  |*|           B          ]
      .par(A.signalPos, B.signalPos)              .to[         (Done |*| A) |*| (Done |*| B)         ]
      .>(IXI)                                     .to[         (Done |*| Done) |*| (A |*| B)         ]
      .>.fst(raceCompletion)                      .to[         (Done |+| Done) |*| (A |*| B)         ]
      .distributeRL                               .to[ (Done |*| (A |*| B)) |+| (Done |*| (A |*| B)) ]
      .>.left(XI.>.snd(B.awaitPos))               .to[           (A |*| B)  |+| (Done |*| (A |*| B)) ]
      .>.right(|*|.assocRL.>.fst(A.awaitPos))     .to[           (A |*| B) |+|            (A |*| B)  ]

  def race[A: SignalingJunction.Positive, B: SignalingJunction.Positive, C](
    caseFstWins: (A |*| B) -⚬ C,
    caseSndWins: (A |*| B) -⚬ C,
  ): (A |*| B) -⚬ C =
    race[A, B] >>> either(caseFstWins, caseSndWins)

  def raceAgainstL[A](implicit A: SignalingJunction.Positive[A]): (Done |*| A) -⚬ (A |+| A) =
    id                                               [  Done        |*|            A  ]
      .>.snd(A.signalPos).assocRL                 .to[ (Done        |*|  Done) |*| A  ]
      .>.fst(raceCompletion)                      .to[ (Done        |+|  Done) |*| A  ]
      .distributeRL                               .to[ (Done |*| A) |+| (Done  |*| A) ]
      .bimap(A.awaitPos, A.awaitPos)              .to[           A  |+|            A  ]

  def raceAgainstR[A](implicit A: SignalingJunction.Positive[A]): (A |*| Done) -⚬ (A |+| A) =
    swap >>> raceAgainstL >>> |+|.swap

  def select[A, B](implicit
    A: SignalingJunction.Negative[A],
    B: SignalingJunction.Negative[B],
  ): ((A |*| B) |&| (A |*| B)) -⚬ (A |*| B) =
    id                                   [ (A |*|           B ) |&|           (A |*| B)  ]
      .>.choiceL.snd(B.awaitNeg)      .to[ (A |*| (Need |*| B)) |&|           (A |*| B)  ]
      .>.choiceL(XI)                  .to[ (Need |*| (A |*| B)) |&|           (A |*| B)  ]
      .>.choiceR.fst(A.awaitNeg)      .to[ (Need |*| (A |*| B)) |&| ((Need |*| A) |*| B) ]
      .>.choiceR.assocLR              .to[ (Need |*| (A |*| B)) |&| (Need |*| (A |*| B)) ]
      .coDistributeR                  .to[         (Need |&| Need) |*| (A |*| B)         ]
      .>.fst(selectRequest)           .to[         (Need |*| Need) |*| (A |*| B)         ]
      .>(IXI)                         .to[         (Need |*| A) |*| (Need |*| B)         ]
      .par(A.signalNeg, B.signalNeg)  .to[                   A  |*|           B          ]

  def select[Z, A: SignalingJunction.Negative, B: SignalingJunction.Negative](
    caseFstWins: Z -⚬ (A |*| B),
    caseSndWins: Z -⚬ (A |*| B),
  ): Z -⚬ (A |*| B) =
    choice(caseFstWins, caseSndWins) >>> select[A, B]

  def selectAgainstL[A](implicit A: SignalingJunction.Negative[A]): (A |&| A) -⚬ (Need |*| A) =
    id                                               [  Need        |*|            A  ]
      .<.snd(A.signalNeg).<(|*|.assocLR)        .from[ (Need        |*|  Need) |*| A  ]
      .<.fst(selectRequest)                     .from[ (Need        |&|  Need) |*| A  ]
      .<(coDistributeR)                         .from[ (Need |*| A) |&| (Need  |*| A) ]
      .<(|&|.bimap(A.awaitNeg, A.awaitNeg))     .from[           A  |&|            A  ]

  def selectAgainstR[A](implicit A: SignalingJunction.Negative[A]): (A |&| A) -⚬ (A |*| Need) =
    |&|.swap >>> selectAgainstL >>> swap

  def raceSignaledOrNot[A](implicit A: SignalingJunction.Positive[A]): A -⚬ (A |+| A) =
    id                                           [  A                             ]
      .>(A.signalPosSnd)                      .to[  A |*|  Done                   ]
      .>.snd(introSnd(done))                  .to[  A |*| (Done  |*|        Done) ]
      .>.snd(raceCompletion)                  .to[  A |*| (Done  |+|        Done) ]
      .distributeLR                           .to[ (A |*|  Done) |+| (A |*| Done) ]
      .bimap(A.awaitPosSnd, A.awaitPosSnd)    .to[  A           |+|  A            ]

  def selectSignaledOrNot[A](implicit A: SignalingJunction.Negative[A]): (A |&| A) -⚬ A =
    id                                           [  A            |&|  A           ]
      .bimap(A.awaitNegSnd, A.awaitNegSnd)    .to[ (A |*|  Need) |&| (A |*| Need) ]
      .coDistributeL                          .to[  A |*| (Need  |&|        Need) ]
      .>.snd(selectRequest)                   .to[  A |*| (Need  |*|        Need) ]
      .>.snd(elimSnd(need))                   .to[  A |*|  Need                   ]
      .>(A.signalNegSnd)                      .to[  A                             ]

  trait Getter[S, A] { self =>
    def getL[B](that: Getter[A, B])(implicit B: Cosemigroup[B]): S -⚬ (B |*| S)

    def extendJunction(implicit A: Junction.Positive[A]): Junction.Positive[S]

    def getL(implicit A: Cosemigroup[A]): S -⚬ (A |*| S) =
      getL(Getter.identity[A])

    def getR(implicit A: Cosemigroup[A]): S -⚬ (S |*| A) =
      getL >>> swap

    def joinL(implicit A: Junction.Positive[A]): (Done |*| S) -⚬ S =
      extendJunction(A).awaitPosFst

    def joinR(implicit A: Junction.Positive[A]): (S |*| Done) -⚬ S =
      swap >>> joinL(A)

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
          id[S |+| T].bimap(self.getL(next), that.getL(next)) >>> factorL

        override def extendJunction(implicit A: Junction.Positive[A]): Junction.Positive[S |+| T] =
          new Junction.Positive[S |+| T] {
            override def awaitPosFst: (Done |*| (S |+| T)) -⚬ (S |+| T) =
              distributeLR.bimap(self.joinL(A), that.joinL(A))
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
      introFst[S] >>> modify[One, Y](elimFst >>> f)

    def write[X](f: (X |*| A) -⚬ A): (X |*| S) -⚬ S =
      modify[X, One](f >>> introFst) >>> elimFst

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
          distributeLR[X, S, T].bimap(Lens.this.modify(f), that.modify(f)) >>> factorL
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
      swap[F[A], B] >>> inL >>> lift(swap[B, A])

    def outR[A, B]: F[A |*| B] -⚬ (F[A] |*| B) =
      lift(swap[A, B]) >>> outL >>> swap[B, F[A]]

    def getL[A](implicit A: Cosemigroup[A]): F[A] -⚬ (A |*| F[A]) =
      lift(A.split) >>> outL

    def getR[A](implicit A: Cosemigroup[A]): F[A] -⚬ (F[A] |*| A) =
      getL[A] >>> swap

    def lens[A]: Lens[F[A], A] = new Lens[F[A], A] {
      def modify[X, Y](f: (X |*| A) -⚬ (Y |*| A)): (X |*| F[A]) -⚬ (Y |*| F[A]) =
        inL >>> lift(f) >>> outL
    }
  }

  type Id[A] = A

  implicit val idFunctor: Transportive[Id] = new Transportive[Id] {
    def lift[A, B](f: A -⚬ B): Id[A] -⚬ Id[B] = f
    def inL[A, B]: (A |*| Id[B]) -⚬ Id[A |*| B] = id
    def outL[A, B]: Id[A |*| B] -⚬ (A |*| Id[B]) = id
  }

  object |*| {
    def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C)) = dsl.timesAssocLR
    def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C) = dsl.timesAssocRL

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |*| C) -⚬ (B |*| D) =
      par(f, g)

    val bifunctor: Bifunctor[|*|] =
      new Bifunctor[|*|] {
        def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |*| C) -⚬ (B |*| D) =
          bimap(f, g)
      }

    /** Product is covariant in the first argument. */
    def fst[B]: Transportive[λ[x => x |*| B]] =
      new Transportive[λ[x => x |*| B]] {
        def lift[A1, A2](f: A1 -⚬ A2): (A1 |*| B) -⚬ (A2 |*| B) = par(f, id)
        def inL[A1, A2]: (A1 |*| (A2 |*| B)) -⚬ ((A1 |*| A2) |*| B) = assocRL
        def outL[A1, A2]: ((A1 |*| A2) |*| B) -⚬ (A1 |*| (A2 |*| B)) = assocLR
      }

    /** Product is covariant in the second argument. */
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
    def assocLR[A, B, C]: ((A |+| B) |+| C) -⚬ (A |+| (B |+| C)) = dsl.plusAssocLR
    def assocRL[A, B, C]: (A |+| (B |+| C)) -⚬ ((A |+| B) |+| C) = dsl.plusAssocRL

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |+| C )-⚬ (B |+| D) =
      either(f > injectL, g > injectR)

    def swap[A, B]: (A |+| B) -⚬ (B |+| A) =
      either(injectR, injectL)

    def IXI[A, B, C, D]: ((A |+| B) |+| (C |+| D)) -⚬ ((A |+| C) |+| (B |+| D)) =
      either(
        either(injectL ⚬ injectL, injectR ⚬ injectL),
        either(injectL ⚬ injectR, injectR ⚬ injectR),
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
    def assocLR[A, B, C]: ((A |&| B) |&| C) -⚬ (A |&| (B |&| C)) = dsl.choiceAssocLR
    def assocRL[A, B, C]: (A |&| (B |&| C)) -⚬ ((A |&| B) |&| C) = dsl.choiceAssocRL

    def bimap[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |&| C) -⚬ (B |&| D) =
      choice(chooseL > f, chooseR > g)

    def swap[A, B]: (A |&| B) -⚬ (B |&| A) =
      choice(chooseR, chooseL)

    def IXI[A, B, C, D]: ((A |&| B) |&| (C |&| D)) -⚬ ((A |&| C) |&| (B |&| D)) =
      choice(
        choice(chooseL >>> chooseL, chooseR >>> chooseL),
        choice(chooseL >>> chooseR, chooseR >>> chooseR),
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

  implicit def fst[B]: Transportive[λ[x => x |*| B]] = |*|.fst[B]
  implicit def snd[A]: Transportive[λ[x => A |*| x]] = |*|.snd[A]

  implicit val tensorBifunctor: Bifunctor[|*|] = |*|.bifunctor

  implicit val eitherBifunctor: Bifunctor[|+|] = |+|.bifunctor

  implicit val choiceBifunctor: Bifunctor[|&|] = |&|.bifunctor

  implicit class LinearFunctionOps[A, B](self: A -⚬ B) {
    /** No-op used for documentation purposes: explicitly states the input type of this linear function. */
    def from[Z](implicit ev: A =:= Z): Z -⚬ B = ev.substituteCo[λ[x => x -⚬ B]](self)

    /** No-op used for documentation purposes: explicitly states the output type of this linear function. */
    def to[C](implicit ev: B =:= C): A -⚬ C = ev.substituteCo(self)

    /** No-op used for documentation purposes: explicitly states the full type of this linear function. */
    def as[C](implicit ev: (A -⚬ B) =:= C): C = ev(self)

    def ⚬[Z](g: Z -⚬ A): Z -⚬ B = dsl.andThen(g, self)

    def bimap[F[_, _]]: BimapSyntax[F, A, B] =
      new BimapSyntax[F, A, B](self)

    def >>>[C](g: B -⚬ C): A -⚬ C =
      dsl.andThen(self, g)

    def injectL[C]: A -⚬ (B |+| C) =
      dsl.andThen(self, dsl.injectL)

    def injectR[C]: A -⚬ (C |+| B) =
      dsl.andThen(self, dsl.injectR)

    def either[B1, B2, C](f: B1 -⚬ C, g: B2 -⚬ C)(implicit ev: B =:= (B1 |+| B2)): A -⚬ C =
      dsl.andThen(ev.substituteCo(self), dsl.either(f, g))

    def chooseL[B1, B2](implicit ev: B =:= (B1 |&| B2)): A -⚬ B1 =
      ev.substituteCo(self) >>> dsl.chooseL

    def chooseR[B1, B2](implicit ev: B =:= (B1 |&| B2)): A -⚬ B2 =
      ev.substituteCo(self) >>> dsl.chooseR

    def choice[C, D](f: B -⚬ C, g: B -⚬ D): A -⚬ (C |&| D) =
      self >>> dsl.choice(f, g)

    def par[B1, B2, C, D](f: B1 -⚬ C, g: B2 -⚬ D)(implicit ev: B =:= (B1 |*| B2)): A -⚬ (C |*| D) =
      ev.substituteCo(self) >>> dsl.par(f, g)

    def elimFst[B2](implicit ev: B =:= (One |*| B2)): A -⚬ B2 =
      ev.substituteCo(self) >>> dsl.elimFst

    def elimFst[B1, B2](f: B1 -⚬ One)(implicit ev: B =:= (B1 |*| B2)): A -⚬ B2 =
      ev.substituteCo(self) >>> dsl.elimFst(f)

    def elimSnd[B1](implicit ev: B =:= (B1 |*| One)): A -⚬ B1 =
      ev.substituteCo(self) >>> dsl.elimSnd

    def elimSnd[B1, B2](f: B2 -⚬ One)(implicit ev: B =:= (B1 |*| B2)): A -⚬ B1 =
      ev.substituteCo(self) >>> dsl.elimSnd(f)

    def introFst: A -⚬ (One |*| B) =
      self >>> dsl.introFst

    def introFst[C](f: One -⚬ C): A -⚬ (C |*| B) =
      self >>> dsl.introFst(f)

    def introSnd: A -⚬ (B |*| One) =
      self >>> dsl.introSnd

    def introSnd[C](f: One -⚬ C): A -⚬ (B |*| C) =
      self >>> dsl.introSnd(f)

    def swap[B1, B2](implicit ev: B =:= (B1 |*| B2)): A -⚬ (B2 |*| B1) =
      ev.substituteCo(self) >>> dsl.swap

    def distributeLR[B1, B2, B3](implicit ev: B =:= (B1 |*| (B2 |+| B3))): A -⚬ ((B1 |*| B2) |+| (B1 |*| B3)) =
      ev.substituteCo(self) >>> dsl.distributeLR

    def distributeRL[B1, B2, B3](implicit ev: B =:= ((B1 |+| B2) |*| B3)): A -⚬ ((B1 |*| B3) |+| (B2 |*| B3)) =
      ev.substituteCo(self) >>> dsl.distributeRL

    def factorL[C, D1, D2](implicit ev: B =:= ((C |*| D1) |+| (C |*| D2))): A -⚬ (C |*| (D1 |+| D2)) =
      ev.substituteCo(self) >>> dsl.factorL

    def factorR[C1, C2, D](implicit ev: B =:= ((C1 |*| D) |+| (C2 |*| D))): A -⚬ ((C1 |+| C2) |*| D) =
      ev.substituteCo(self) >>> dsl.factorR

    def coDistributeL[B1, B2, B3](implicit ev: B =:= ((B1 |*| B2) |&| (B1 |*| B3))): A -⚬ (B1 |*| (B2 |&| B3)) =
      ev.substituteCo(self) >>> dsl.coDistributeL

    def coDistributeR[B1, B2, B3](implicit ev: B =:= ((B1 |*| B3) |&| (B2 |*| B3))): A -⚬ ((B1 |&| B2) |*| B3) =
      ev.substituteCo(self) >>> dsl.coDistributeR

    def coFactorL[B1, B2, B3](implicit ev: B =:= (B1 |*| (B2 |&| B3))): A -⚬ ((B1 |*| B2) |&| (B1 |*| B3)) =
      ev.substituteCo(self) >>> dsl.coFactorL

    def coFactorR[B1, B2, B3](implicit ev: B =:= ((B1 |&| B2) |*| B3)): A -⚬ ((B1 |*| B3) |&| (B2 |*| B3)) =
      ev.substituteCo(self) >>> dsl.coFactorR

    def pack[F[_]](implicit ev: B =:= F[Rec[F]]): A -⚬ Rec[F] =
      ev.substituteCo(self) >>> dsl.pack[F]

    def unpack[F[_]](implicit ev: B =:= Rec[F]): A -⚬ F[Rec[F]] =
      ev.substituteCo(self) >>> dsl.unpack[F]

    def race[B1: SignalingJunction.Positive, B2: SignalingJunction.Positive, C](
      caseFstWins: (B1 |*| B2) -⚬ C,
      caseSndWins: (B1 |*| B2) -⚬ C,
    )(implicit
      ev: B =:= (B1 |*| B2),
    ): A -⚬ C =
      ev.substituteCo(self) >>> lib.race(caseFstWins, caseSndWins)

    def select[C1: SignalingJunction.Negative, C2: SignalingJunction.Negative](
      caseFstWins: B -⚬ (C1 |*| C2),
      caseSndWins: B -⚬ (C1 |*| C2),
    ): A -⚬ (C1 |*| C2) =
      self >>> lib.select(caseFstWins, caseSndWins)

    /** Focuses on function's output. */
    def > : FocusedCo[[x] =>> A -⚬ x, B] =
      new FocusedCo[[x] =>> A -⚬ x, B](self)

    /** Focuses on function's input. */
    def < : FocusedContra[[x] =>> x -⚬ B, A] =
      new FocusedContra[[x] =>> x -⚬ B, A](self)
  }

  implicit class LinearFunctionToTimesOps[A, B1, B2](self: A -⚬ (B1 |*| B2)) {
    def assocLR[X, Y](implicit ev: B1 =:= (X |*| Y)): A -⚬ (X |*| (Y |*| B2)) =
      ev.substituteCo[λ[x => A -⚬ (x |*| B2)]](self) >>> |*|.assocLR

    def assocRL[X, Y](implicit ev: B2 =:= (X |*| Y)): A -⚬ ((B1 |*| X) |*| Y) =
      ev.substituteCo[λ[x => A -⚬ (B1 |*| x)]](self) >>> |*|.assocRL

    def joinL(neglect: B1 -⚬ Done)(implicit j: Junction.Positive[B2]): A -⚬ B2 =
      self >>> par(neglect, id[B2]) >>> j.awaitPosFst

    def joinR(neglect: B2 -⚬ Done)(implicit j: Junction.Positive[B1]): A -⚬ B1 =
      self >>> par(id[B1], neglect) >>> j.awaitPosSnd

    def joinL(implicit ev: B1 =:= Done, j: Junction.Positive[B2]): A -⚬ B2 = {
      type F[X] = A -⚬ (X |*| B2)
      ev.substituteCo[F](self) >>> j.awaitPosFst
    }

    def joinR(implicit ev: B2 =:= Done, j: Junction.Positive[B1]): A -⚬ B1 = {
      type F[X] = A -⚬ (B1 |*| X)
      ev.substituteCo[F](self) >>> j.awaitPosSnd
    }
  }

  implicit class LinearFunctionToPlusOps[A, B1, B2](self: A -⚬ (B1 |+| B2)) {
    def assocLR[X, Y](implicit ev: B1 =:= (X |+| Y)): A -⚬ (X |+| (Y |+| B2)) =
      ev.substituteCo[λ[x => A -⚬ (x |+| B2)]](self) >>> |+|.assocLR

    def assocRL[X, Y](implicit ev: B2 =:= (X |+| Y)): A -⚬ ((B1 |+| X) |+| Y) =
      ev.substituteCo[λ[x => A -⚬ (B1 |+| x)]](self) >>> |+|.assocRL
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

  /** Focused on `B` in the output `F[B]` of linear function `A -⚬ F[B]`, where `B` is in a covariant position. */
  class FocusedCo[F[_], B](f: F[B])(implicit F: Externalizer[F]) {
    def map[C](g: B -⚬ C): F[C] = F.lift(g)(f)

    /** Alias for [[map]]. */
    def apply[C](g: B -⚬ C): F[C] = map(g)

    def subst[C](implicit ev: B =:= C): F[C] =
      ev.substituteCo(f)

    def unsubst[C](implicit ev: C =:= B): F[C] =
      ev.substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(implicit ev: B =:= G[C]): FocusedCo[λ[x => F[G[x]]], C] =
      new FocusedCo[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ⚬ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(implicit ev: B =:= G[C]): FocusedContra[λ[x => F[G[x]]], C] =
      new FocusedContra[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ⚬ G)

    def co[G[_]](implicit G: Functor[G], U: Unapply[B, G]): FocusedCo[λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(U.ev)

    def contra[G[_]](implicit G: ContraFunctor[G], U: Unapply[B, G]): FocusedContra[λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(U.ev)

    def bi[G[_, _]](implicit G: Bifunctor[G], U: Unapply2[B, G]): FocusedBi[λ[(x, y) => F[G[x, y]]], U.A, U.B] =
      new FocusedBi[λ[(x, y) => F[G[x, y]]], U.A, U.B](U.ev.substituteCo(f))(F ⚬ G)

    def injectL[C]: F[B |+| C] = F.lift(dsl.injectL)(f)
    def injectR[C]: F[C |+| B] = F.lift(dsl.injectR)(f)
  }

  class FocusedBi[F[_, _], B1, B2](f: F[B1, B2])(F: BiExternalizer[F]) {
    def fst: FocusedCo[F[*, B2], B1] =
      new FocusedCo[F[*, B2], B1](f)(F.fst)

    def snd: FocusedCo[F[B1, *], B2] =
      new FocusedCo[F[B1, *], B2](f)(F.snd)
  }

  implicit class FocusedOnTimesCo[F[_], B1, B2](f: FocusedCo[F, B1 |*| B2]) {
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

    def joinL(neglect: B1 -⚬ Done)(implicit j: Junction.Positive[B2]): F[B2] =
      f(par(neglect, id[B2]) >>> j.awaitPosFst)

    def joinR(neglect: B2 -⚬ Done)(implicit j: Junction.Positive[B1]): F[B1] =
      f(par(id[B1], neglect) >>> j.awaitPosSnd)
  }

  implicit class FocusedOnDoneTimesCo[F[_], B2](f: FocusedCo[F, Done |*| B2])(implicit j: Junction.Positive[B2]) {
    def joinL: F[B2] = f(j.awaitPosFst)
  }

  implicit class FocusedOnTimesDoneCo[F[_], B1](f: FocusedCo[F, B1 |*| Done])(implicit j: Junction.Positive[B1]) {
    def joinR: F[B1] = f(j.awaitPosSnd)
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
      new FocusedContra[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ⚬ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(implicit ev: B =:= G[C]): FocusedCo[λ[x => F[G[x]]], C] =
      new FocusedCo[λ[x => F[G[x]]], C](ev.substituteCo(f))(F ⚬ G)

    def co[G[_]](implicit G: Functor[G], U: Unapply[B, G]): FocusedContra[λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(U.ev)

    def contra[G[_]](implicit G: ContraFunctor[G], U: Unapply[B, G]): FocusedCo[λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(U.ev)
  }

  implicit class FocusedOnTimesContra[A, F[_], B1, B2](f: FocusedContra[F, B1 |*| B2]) {
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
    |*|.assocLR[A, B, C] >>> par(id, swap) >>> |*|.assocRL

  def XI[A, B, C]: (A |*|(B|*|C)) -⚬
    //               \   /    |
    //                \ /     |
    //                 X      |
    //                / \     |
    //               /   \    |
                   (B |*|(A|*|C)) =
    |*|.assocRL[A, B, C] >>> par(swap, id) >>> |*|.assocLR

  /** From the choice ''available'' on the right (`C |&| D`), choose the one corresponding to the choice ''made''
    * on the left (`A |+| B`): if on the left there is `A`, choose `C`, if on the left thre is `B`, choose `D`.
    */
  def matchingChoiceLR[A, B, C, D]: ((A |+| B) |*| (C |&| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |+| B) |*| (C |&| D)]
      .distributeRL            .to[(A |*| (C |&| D)) |+| (B |*| (C |&| D))]
      .>.left.snd(chooseL)     .to[(A |*|  C       ) |+| (B |*| (C |&| D))]
      .>.right.snd(chooseR)    .to[(A |*|  C       ) |+| (B |*|        D )]

  /** From the choice ''available'' on the left (`A |&| B`), choose the one corresponding to the choice ''made''
    * on the right (`C |+| D`): if on the right there is `C`, choose `A`, if on the right there is `D`, choose `B`.
    */
  def matchingChoiceRL[A, B, C, D]: ((A |&| B) |*| (C |+| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |&| B) |*| (C |+| D)]
      .distributeLR            .to[((A |&| B) |*| C) |+| ((A |&| B) |*| D)]
      .>.left.fst(chooseL)     .to[( A        |*| C) |+| ((A |&| B) |*| D)]
      .>.right.fst(chooseR)    .to[( A        |*| C) |+| (       B  |*| D)]

  /** Present a choice between two products (`(A |*| B) |&| (C |*| D)`) as a choice (`A |&| C`) between the first
    * components of the respective products and provide the second component corresponding to the chosen first
    * component on the side (as `B |+| D`).
    */
  def subordinateSnd[A, B, C, D]: ((A |*| B) |&| (C |*| D)) -⚬ ((A |&| C) |*| (B |+| D)) =
    id                                 [ (A |*|  B       ) |&| (C |*|        D ) ]
      .>.choiceL.snd.injectL[D]     .to[ (A |*| (B |+| D)) |&| (C |*|        D ) ]
      .>.choiceR.snd.injectR[B]     .to[ (A |*| (B |+| D)) |&| (C |*| (B |+| D)) ]
      .coDistributeR

  /** Present a choice between two products (`(A |*| B) |&| (C |*| D)`) as a choice (`B |&| D`) between the second
    * components of the respective products and provide the first component corresponding to the chosen second
    * component on the side (as `A |+| C`).
    */
  def subordinateFst[A, B, C, D]: ((A |*| B) |&| (C |*| D)) -⚬ ((A |+| C) |*| (B |&| D)) =
    id                                 [ ( A        |*|  B) |&| (       C  |*| D) ]
      .>.choiceL.fst.injectL[C]     .to[ ((A |+| C) |*|  B) |&| (       C  |*| D) ]
      .>.choiceR.fst.injectR[A]     .to[ ((A |+| C) |*|  B) |&| ((A |+| C) |*| D) ]
      .coDistributeL                .to[  (A |+| C) |*| (B  |&|                D) ]

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

  def delayEitherUntilDone[A, B]: (Done |*| (A |+| B)) -⚬ ((Done |*| A) |+| (Done |*| B)) =
    id                                                               [  Done |*| (A  |+|           B) ]
      .distributeLR                                               .to[ (Done |*|  A) |+| (Done |*| B) ]
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

  def joinInjectL[A, B](implicit A: Junction.Positive[A]): (Done |*| A) -⚬ (A |+| B) =
    injectLWhenDone.>.left(A.awaitPos)

  def joinInjectR[A, B](implicit B: Junction.Positive[B]): (Done |*| B) -⚬ (A |+| B) =
    injectRWhenDone.>.right(B.awaitPos)

  def cojoinChooseL[A, B](implicit A: Junction.Negative[A]): (A |&| B) -⚬ (Need |*| A) =
    id[A |&| B].>.choiceL(A.awaitNeg) >>> chooseLWhenNeed

  def cojoinChooseR[A, B](implicit B: Junction.Negative[B]): (A |&| B) -⚬ (Need |*| B) =
    id[A |&| B].>.choiceR(B.awaitNeg) >>> chooseRWhenNeed

  def joinChooseL[A, B](implicit A: Junction.Positive[A]): (Done |*| (A |&| B)) -⚬ A =
    par(id, cojoinChooseL(Junction.invert(A))).assocRL.elimFst(rInvertSignal)

  def joinChooseR[A, B](implicit B: Junction.Positive[B]): (Done |*| (A |&| B)) -⚬ B =
    par(id, cojoinChooseR(Junction.invert(B))).assocRL.elimFst(rInvertSignal)

  /** Creates a pair of mutually recursive functions. */
  def rec2[A, B, C, D](
    f: (A -⚬ B, C -⚬ D) => A -⚬ B,
    g: (A -⚬ B, C -⚬ D) => C -⚬ D,
  ): (A -⚬ B, C -⚬ D) =
    (
      rec { (ab: A -⚬ B) => f(ab, rec { (cd: C -⚬ D) => g(ab, cd) }) },
      rec { (cd: C -⚬ D) => g(rec { (ab: A -⚬ B) => f(ab, cd) }, cd) },
    )

  type Bool = Done |+| Done
  object Bool {
    val constTrue: One -⚬ Bool =
      done >>> injectL

    val constFalse: One -⚬ Bool =
      done >>> injectR

    def switch[R](
      caseTrue : Done -⚬ R,
      caseFalse: Done -⚬ R,
    ): Bool -⚬ R =
      either(caseTrue, caseFalse)

    def switchWithL[A, R](
      caseTrue : (A |*| Done) -⚬ R,
      caseFalse: (A |*| Done) -⚬ R,
    ): (A |*| Bool) -⚬ R =
      distributeLR.either(caseTrue, caseFalse)

    def switchWithR[A, R](
      caseTrue : (Done |*| A) -⚬ R,
      caseFalse: (Done |*| A) -⚬ R,
    ): (Bool |*| A) -⚬ R =
      distributeRL.either(caseTrue, caseFalse)

    def ifThenElse[A, B, C](ifTrue: (Done |*| A) -⚬ B, ifFalse: (Done |*| A) -⚬ C): (Bool |*| A) -⚬ (B |+| C) =
      id                                   [          Bool |*| A           ]
        .distributeRL                   .to[ (Done |*| A) |+| (Done |*| A) ]
        .bimap(ifTrue, ifFalse)         .to[        B     |+|        C     ]
  }

  import Bool._

  def testBy[A, B, K: Cosemigroup: Junction.Positive](
    aKey: Getter[A, K],
    bKey: Getter[B, K],
    pred: (K |*| K) -⚬ Bool,
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) = {
    val awaitL: (Done |*| (A |*| B)) -⚬ (A |*| B) =
      (aKey compose |*|.fst[B].lens[A]).joinL

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
    def equiv[A, B]: (A |*| B) -⚬ Compared[A, B] = injectL >>> injectR
    def gt   [A, B]: (A |*| B) -⚬ Compared[A, B] = injectR >>> injectR

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
        .distributeRL.>.right(distributeRL)     .to[ ((A |*| B) |*| C) |+| (((A |*| B) |*| C) |+| ((A |*| B)   |*| C)) ]
        .either(caseLt, either(caseEq, caseGt)) .to[                    D                                              ]

    def enrichWith[A, B, C, S, T](
      f: ((A |*| B) |*| C) -⚬ (S |*| T),
    )
    : (Compared[A, B] |*| C) -⚬ Compared[S, T] =
      id[ Compared[A, B] |*| C ]                .to[ ((A |*| B)        |+| ( (A |*| B)        |+|  (A |*| B))) |*| C   ]
        .distributeRL.>.right(distributeRL)     .to[ ((A |*| B) |*| C) |+| (((A |*| B) |*| C) |+| ((A |*| B)   |*| C)) ]
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
          id                           [ (A    |*| B) |*| (S    |*| T) ]
            .>(IXI)                 .to[ (A    |*| S) |*| (B    |*| T) ]
            .>.fst.fst(A.counit)    .to[ (Done |*| S) |*| (B    |*| T) ]
            .>.snd.fst(B.counit)    .to[ (Done |*| S) |*| (Done |*| T) ]
            .par(f.joinL, g.joinL)  .to[           S  |*|           T  ]

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

  def rInvertTimes[A, B, Ȧ, Ḃ](
    rInvertA: (A |*| Ȧ) -⚬ One,
    rInvertB: (B |*| Ḃ) -⚬ One,
  ): ((A |*| B) |*| (Ȧ |*| Ḃ)) -⚬ One =
    id[(A |*| B) |*| (Ȧ |*| Ḃ)]               .to[ (A |*| B) |*| (Ȧ |*| Ḃ) ]
      .>(IXI)                                 .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
      .>(parToOne(rInvertA, rInvertB))        .to[           One           ]

  def lInvertTimes[A, B, Ȧ, Ḃ](
    lInvertA: One -⚬ (Ȧ |*| A),
    lInvertB: One -⚬ (Ḃ |*| B),
  ): One -⚬ ((Ȧ |*| Ḃ) |*| (A |*| B)) =
    id[One]                                   .to[           One           ]
      .>(parFromOne(id, id))                  .to[    One    |*|    One    ]
      .par(lInvertA, lInvertB)                .to[ (Ȧ |*| A) |*| (Ḃ |*| B) ]
      .>(IXI)                                 .to[ (Ȧ |*| Ḃ) |*| (A |*| B) ]

  implicit def productDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |*| B, Ȧ |*| Ḃ] =
    new Dual[A |*| B, Ȧ |*| Ḃ] {
      val lInvert: One -⚬ ((Ȧ |*| Ḃ) |*| (A |*| B)) =
        lInvertTimes(a.lInvert, b.lInvert)

      val rInvert: ((A |*| B) |*| (Ȧ |*| Ḃ)) -⚬ One =
        rInvertTimes(a.rInvert, b.rInvert)
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
      par(unpack, unpack) >>> rInvertSub(self)
    }

  def lInvertRec[F[_], G[_]](
    lInvertSub: [x, y] => (One -⚬ (x |*| y)) => (One -⚬ (F[x] |*| G[y])),
  ): One -⚬ (Rec[F] |*| Rec[G]) =
    rec { self =>
      lInvertSub(self) >>> par(pack, pack)
    }

  /** If `F[A]` is dual to `G[B]` for all dual pairs `A`, `B`, then `Rec[F]` is dual to `Rec[G]`. */
  def dualRec[F[_], G[_]](ev: Dual1[F, G]): Dual[Rec[F], Rec[G]] =
    new Dual[Rec[F], Rec[G]] {
      val rInvert: (Rec[F] |*| Rec[G]) -⚬ One =
        rInvertRec(ev.rInvertVal)

      val lInvert: One -⚬ (Rec[G] |*| Rec[F]) =
        lInvertRec(ev.lInvertFlippedTArgs)
    }

  type Maybe[A] = One |+| A
  object Maybe {
    def empty[A]: One -⚬ Maybe[A] =
      injectL

    def just[A]: A -⚬ Maybe[A] =
      injectR

    def getOrElse[A](f: One -⚬ A): Maybe[A] -⚬ A =
      either(f, id)

    def discard[A](f: A -⚬ One): Maybe[A] -⚬ One =
      either(id, f)

    def discard[A](implicit A: Comonoid[A]): Maybe[A] -⚬ One =
      discard(A.counit)

    def neglect[A](f: A -⚬ Done): Maybe[A] -⚬ Done =
      either(done, f)
  }

  type Optional[A] = One |&| A
  object Optional {
    def optOut[A]: Optional[A] -⚬ One =
      chooseL

    def optIn[A]: Optional[A] -⚬ A =
      chooseR

    def fromDiscardable[A](discard: A -⚬ One): A -⚬ Optional[A] =
      choice(discard, id)
  }

  type PMaybe[A] = Done |+| A
  object PMaybe {
    def empty[A]: Done -⚬ PMaybe[A] =
      injectL

    def just[A]: A -⚬ PMaybe[A] =
      injectR

    def getOrElse[A](f: Done -⚬ A): PMaybe[A] -⚬ A =
      either(f, id)

    def neglect[A](f: A -⚬ Done): PMaybe[A] -⚬ Done =
      either(id, f)

    def neglect[A](implicit A: PComonoid[A]): PMaybe[A] -⚬ Done =
      neglect(A.counit)
  }

  def parFromOne[A, B](f: One -⚬ A, g: One -⚬ B): One -⚬ (A |*| B) =
    introSnd[One] > par(f, g)

  def parToOne[A, B](f: A -⚬ One, g: B -⚬ One): (A |*| B) -⚬ One =
    par(f, g) > elimSnd[One]

  type MultipleF[A, X] = One |+| (A |+| (X |*| X))

  /** Zero or more instances of `A`. The exact multiplicity is determined by the producer. */
  type Multiple[A] = Rec[MultipleF[A, *]]
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
  }

  type UnlimitedF[A, X] = One |&| (A |&| (X |*| X))

  /** Unlimited supply of `A`s. The consumer chooses how many `A`s to consume. */
  type Unlimited[A] = Rec[UnlimitedF[A, *]]
  object Unlimited {
    def discard[A]: Unlimited[A] -⚬ One =
      unpack[UnlimitedF[A, *]] > chooseL

    def single[A]: Unlimited[A] -⚬ A =
      unpack[UnlimitedF[A, *]] > chooseR > chooseL

    def double[A]: Unlimited[A] -⚬ (Unlimited[A] |*| Unlimited[A]) =
      unpack[UnlimitedF[A, *]] > chooseR > chooseR

    def create[X, A](
      case0: X -⚬ One,
      case1: X -⚬ A,
      caseN: X -⚬ (Unlimited[A] |*| Unlimited[A]),
    ): X -⚬ Unlimited[A] =
      choice(case0, choice(case1, caseN)) > pack[UnlimitedF[A, *]]

    def duplicate[A]: Unlimited[A] -⚬ Unlimited[Unlimited[A]] = rec { self =>
      create(
        case0 = discard,
        case1 = id,
        caseN = double > par(self, self)
      )
    }
  }

  type PUnlimitedF[A, X] = Done |&| (A |&| (X |*| X))
  type PUnlimited[A] = Rec[PUnlimitedF[A, *]]
  object PUnlimited {
    def neglect[A]: PUnlimited[A] -⚬ Done =
      unpack[PUnlimitedF[A, *]] > chooseL

    def single[A]: PUnlimited[A] -⚬ A =
      unpack[PUnlimitedF[A, *]] > chooseR > chooseL

    def double[A]: PUnlimited[A] -⚬ (PUnlimited[A] |*| PUnlimited[A]) =
      unpack[PUnlimitedF[A, *]] > chooseR > chooseR

    def create[X, A](
      case0: X -⚬ Done,
      case1: X -⚬ A,
      caseN: X -⚬ (PUnlimited[A] |*| PUnlimited[A]),
    ): X -⚬ PUnlimited[A] =
      choice(case0, choice(case1, caseN)) > pack[PUnlimitedF[A, *]]

    def duplicate[A]: PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] = rec { self =>
      create(
        case0 = neglect,
        case1 = id,
        caseN = double > par(self, self)
      )
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

    implicit def nAffineTimes[A, B](implicit A: NAffine[A], B: NAffine[B]): NAffine[A |*| B] =
      from(par(A.deflate, B.deflate) >>> forkNeed)
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
      from(A.deflate >>> need)

    implicit def affineTimes[A, B](implicit A: Affine[A], B: Affine[B]): Affine[A |*| B] =
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
      from(A.discard >>> done)

    implicit val pAffineDone: PAffine[Done] =
      from(id)

    implicit def pAffineTimes[A, B](implicit A: PAffine[A], B: PAffine[B]): PAffine[A |*| B] =
      from(par(A.neglect, B.neglect) >>> join)
  }

  trait Semigroup[A] {
    def combine: (A |*| A) -⚬ A

    def law_associativity: Equal[ ((A |*| A) |*| A) -⚬ A ] =
      Equal(
        par(combine, id[A]) >>> combine,
        |*|.assocLR >>> par(id[A], combine) >>> combine,
      )
  }

  trait Cosemigroup[A] {
    def split: A -⚬ (A |*| A)

    def law_coAssociativity: Equal[ A -⚬ ((A |*| A) |*| A) ] =
      Equal(
        split >>> par(split, id[A]),
        split >>> par(id[A], split) >>> |*|.assocRL,
      )
  }

  trait Monoid[A] extends Semigroup[A] {
    def unit: One -⚬ A

    def law_leftUnit: Equal[ (One |*| A) -⚬ A ] =
      Equal(
        par(unit, id[A]) >>> combine,
        elimFst,
      )

    def law_rightUnit: Equal[ (A |*| One) -⚬ A ] =
      Equal(
        par(id[A], unit) >>> combine,
        elimSnd,
      )
  }

  object Monoid {
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
        split >>> par(counit, id[A]),
        introFst,
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| One) ] =
      Equal(
        split >>> par(id[A], counit),
        introSnd,
      )
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
      def unit: One -⚬ A = done >>> PMonoid.this.unit
    }

    def law_leftUnit: Equal[ (One |*| A) -⚬ A ] =
      Equal(
        par(done >>> unit, id[A]) >>> combine,
        elimFst,
      )

    def law_rightUnit: Equal[ (A |*| One) -⚬ A ] =
      Equal(
        par(id[A], done >>> unit) >>> combine,
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
      def counit: A -⚬ One = NComonoid.this.counit >>> need
    }

    def law_leftCounit: Equal[ A -⚬ (One |*| A) ] =
      Equal(
        split >>> par(counit >>> need, id[A]),
        introFst,
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| One) ] =
      Equal(
        split >>> par(id[A], counit >>> need),
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
        par(regressInfinitely >>> unit, id[A]) >>> combine,
        id[LTerminus |*| A].elimFst(regressInfinitely >>> need),
      )

    def law_rightUnit: Equal[ (A |*| LTerminus) -⚬ A ] =
      Equal(
        par(id[A], regressInfinitely >>> unit) >>> combine,
        id[A |*| LTerminus].elimSnd(regressInfinitely >>> need),
      )
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
        split >>> par(counit >>> delayIndefinitely, id[A]),
        id[A].introFst(done >>> delayIndefinitely),
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| RTerminus) ] =
      Equal(
        split >>> par(id[A], counit >>> delayIndefinitely),
        id[A].introSnd(done >>> delayIndefinitely),
      )
  }

  trait Monad[F[_]] {
    def pure[A]    :       A -⚬ F[A]
    def flatten[A] : F[F[A]] -⚬ F[A]
  }

  trait Comonad[F[_]] {
    def extract[A]   : F[A] -⚬ A
    def duplicate[A] : F[A] -⚬ F[F[A]]
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

  implicit def comonoidUnlimited[A]: Comonoid[Unlimited[A]] =
    new Comonoid[Unlimited[A]] {
      def counit : Unlimited[A] -⚬ One                             = Unlimited.discard
      def split  : Unlimited[A] -⚬ (Unlimited[A] |*| Unlimited[A]) = Unlimited.double
    }

  implicit def pComonoidPUnlimited[A]: PComonoid[PUnlimited[A]] =
    new PComonoid[PUnlimited[A]] {
      def counit : PUnlimited[A] -⚬ Done                              = PUnlimited.neglect
      def split  : PUnlimited[A] -⚬ (PUnlimited[A] |*| PUnlimited[A]) = PUnlimited.double
    }

  implicit val comonadUnlimited: Comonad[Unlimited] =
    new Comonad[Unlimited] {
      def extract[A]   : Unlimited[A] -⚬ A                       = Unlimited.single
      def duplicate[A] : Unlimited[A] -⚬ Unlimited[Unlimited[A]] = Unlimited.duplicate
    }

  implicit val comonadPUnlimited: Comonad[PUnlimited] =
    new Comonad[PUnlimited] {
      def extract[A]   : PUnlimited[A] -⚬ A                         = PUnlimited.single
      def duplicate[A] : PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] = PUnlimited.duplicate
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

  type LListF[T, X] = One |+| (T |*| X)
  type LList[T] = Rec[LListF[T, *]]

  object LList {
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
      unpack[LListF[T, *]]

    def fromList[T](ts: List[One -⚬ T]): One -⚬ LList[T] = {
      @tailrec def go(rts: List[One -⚬ T], acc: One -⚬ LList[T]): One -⚬ LList[T] =
        rts match {
          case head :: tail => go(tail, parFromOne(head, acc) >>> cons)
          case Nil => acc
        }

      go(ts.reverse, nil[T])
    }

    def of[T](ts: (One -⚬ T)*): One -⚬ LList[T] =
      fromList(ts.toList)

    def switch[T, R](
      caseNil: One -⚬ R,
      caseCons: (T |*| LList[T]) -⚬ R,
    ): LList[T] -⚬ R =
      uncons[T].either(caseNil, caseCons)

    def switchWithL[A, T, R](
      caseNil: A -⚬ R,
      caseCons: (A |*| (T |*| LList[T])) -⚬ R,
    ): (A |*| LList[T]) -⚬ R =
      par(id, uncons[T]) > distributeLR > either(elimSnd > caseNil, caseCons)

    def switchWithR[A, T, R](
      caseNil: A -⚬ R,
      caseCons: ((T |*| LList[T]) |*| A) -⚬ R,
    ): (LList[T] |*| A) -⚬ R =
      swap > switchWithL(caseNil, swap > caseCons)

    def map[T, U](f: T -⚬ U): LList[T] -⚬ LList[U] =
      rec { self =>
        switch(nil[U], par(f, self) >>> cons)
      }

    def fold[T](implicit T: Monoid[T]): LList[T] -⚬ T =
      rec { self =>
        switch(T.unit, par(id, self) > T.combine)
      }

    def consMaybe[T]: (Maybe[T] |*| LList[T]) -⚬ LList[T] =
      id[Maybe[T] |*| LList[T]]             .to[ (One |+|                T) |*| LList[T] ]
        .distributeRL                       .to[ (One |*| LList[T]) |+| (T |*| LList[T]) ]
        .>(either(elimFst, cons))           .to[                 LList[T]                ]

    def collect[T, U](f: T -⚬ Maybe[U]): LList[T] -⚬ LList[U] =
      rec { self =>
        switch(nil[U], par(f, self) >>> consMaybe)
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
        par(id, self) >>> IXI >>> par(cons, cons)

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
    ): LList[A] -⚬ LList[B] = {
      def go: (S |*| LList[A]) -⚬ LList[B] = rec { self =>
        switchWithL(
          caseNil  = last > singleton,
          caseCons = |*|.assocRL > par(f, id) > |*|.assocLR > par(id, self) > cons,
        )
      }

      switch(
        caseNil  = nil[B],
        caseCons = par(init, id) > go,
      )
    }

    /** Shifts all the elements of a list by "half" to the left,
     *  moving the first half of the first element to the end of the list.
     *
     *  Example:
     *
     *  Before:
     *  {{{
     *  (a1, b1), (a2, b2), (a3, b3)
     *  }}}
     *
     *  After:
     *  {{{
     *  (b1, a2), (b2, a3), (b3, a1)
     *  }}}
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
  }
}
