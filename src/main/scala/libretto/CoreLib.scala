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
  }

  object Externalizer {
    implicit def outportInstance[A]: Externalizer[[x] =>> A -⚬ x] =
      new Externalizer[[x] =>> A -⚬ x] {
        def lift[B, C](f: B -⚬ C): (A -⚬ B) => (A -⚬ C) =
          _ >>> f
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
    }

    /** Represents ''a'' way how `A` can await (join) a negative (i.e. [[Need]]) signal. */
    trait Negative[A] {
      def awaitNegFst: A -⚬ (Need |*| A)

      def awaitNegSnd: A -⚬ (A |*| Need) =
        awaitNegFst >>> swap

      /** Alias for [[awaitNegFst]]. */
      def awaitNeg: A -⚬ (Need |*| A) =
        awaitNegFst
    }

    object Positive {
      implicit def junctionDone: Junction.Positive[Done] =
        new Junction.Positive[Done] {
          override def awaitPosFst: (Done |*| Done) -⚬ Done =
            join
        }

      def byFst[A, B](implicit A: Junction.Positive[A]): Junction.Positive[A |*| B] =
        new Junction.Positive[A |*| B] {
          override def awaitPosFst: (Done |*| (A |*| B)) -⚬ (A |*| B) =
            |*|.assocRL.>.fst(A.awaitPosFst)
        }

      def eitherInstance[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |+| B] =
        new Junction.Positive[A |+| B] {
          override def awaitPosFst: (Done |*| (A |+| B)) -⚬ (A |+| B) =
            distributeLR[Done, A, B].bimap(A.awaitPosFst, B.awaitPosFst)
        }

      def choiceInstance[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Junction.Positive[A |&| B] =
        new Junction.Positive[A |&| B] {
          override def awaitPosFst: (Done |*| (A |&| B)) -⚬ (A |&| B) =
            coFactorL[Done, A, B].bimap(A.awaitPosFst, B.awaitPosFst)
        }

      def rec[F[_]](implicit F: ∀[λ[x => Junction.Positive[F[x]]]]): Junction.Positive[Rec[F]] =
        new Junction.Positive[Rec[F]] {
          override def awaitPosFst: (Done |*| Rec[F]) -⚬ Rec[F] =
            par(id[Done], unpack[F]) >>> F[Rec[F]].awaitPosFst >>> pack[F]
        }
    }

    object Negative {
      implicit def junctionNeed: Junction.Negative[Need] =
        new Junction.Negative[Need] {
          override def awaitNegFst: Need -⚬ (Need |*| Need) =
            joinNeed
        }

      def byFst[A, B](implicit A: Junction.Negative[A]): Junction.Negative[A |*| B] =
        new Junction.Negative[A |*| B] {
          override def awaitNegFst: (A |*| B) -⚬ (Need |*| (A |*| B)) =
            par(A.awaitNegFst, id[B]).assocLR
        }

      def eitherInstance[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |+| B] =
        new Junction.Negative[A |+| B] {
          override def awaitNegFst: (A |+| B) -⚬ (Need |*| (A |+| B)) =
            id[A |+| B].bimap(A.awaitNegFst, B.awaitNegFst).factorL
        }

      def choiceInstance[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Junction.Negative[A |&| B] =
        new Junction.Negative[A |&| B] {
          override def awaitNegFst: (A |&| B) -⚬ (Need |*| (A |&| B)) =
            id[A |&| B].bimap(A.awaitNegFst, B.awaitNegFst).coDistributeL
        }

      def rec[F[_]](implicit F: ∀[λ[x => Junction.Negative[F[x]]]]): Junction.Negative[Rec[F]] =
        new Junction.Negative[Rec[F]] {
          override def awaitNegFst: Rec[F] -⚬ (Need |*| Rec[F]) =
            (unpack[F] >>> F[Rec[F]].awaitNegFst).>.snd(pack[F])
        }
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
    }

    /** Represents ''a'' way how `A` can produce a negative (i.e. [[Need]]) signal. */
    trait Negative[A] {
      def signalNegFst: (Need |*| A) -⚬ A

      def signalNegSnd: (A |*| Need) -⚬ A =
        swap >>> signalNegFst

      /** Alias for [[signalNegFst]]. */
      def signalNeg: (Need |*| A) -⚬ A =
        signalNegFst
    }

    object Positive {
      implicit def signalingDone: Signaling.Positive[Done] =
        new Signaling.Positive[Done] {
          override def signalPosFst: Done -⚬ (Done |*| Done) =
            fork
        }

      def byFst[A, B](implicit A: Signaling.Positive[A]): Signaling.Positive[A |*| B] =
        new Signaling.Positive[A |*| B] {
          override def signalPosFst: (A |*| B) -⚬ (Done |*| (A |*| B)) =
            par(A.signalPosFst, id[B]).assocLR
        }

      /** Signals when it is decided which side of the [[|+|]] is present. */
      def either[A, B]: Signaling.Positive[A |+| B] =
        new Signaling.Positive[A |+| B] {
          override def signalPosFst: (A |+| B) -⚬ (Done |*| (A |+| B)) =
            dsl.signalEither[A, B]
        }

      def rec[F[_]](implicit F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        new Positive[Rec[F]] {
          override def signalPosFst: Rec[F] -⚬ (Done |*| Rec[F]) =
            (unpack[F] >>> F[Rec[F]].signalPosFst).>.snd(pack[F])
        }
    }

    object Negative {
      implicit def signalingNeed: Signaling.Negative[Need] =
        new Signaling.Negative[Need] {
          override def signalNegFst: (Need |*| Need) -⚬ Need =
            forkNeed
        }

      def byFst[A, B](implicit A: Signaling.Negative[A]): Signaling.Negative[A |*| B] =
        new Signaling.Negative[A |*| B] {
          override def signalNegFst: (Need |*| (A |*| B)) -⚬ (A |*| B) =
            |*|.assocRL.>.fst(A.signalNegFst)
        }

      /** Signals when the choice is made between [[A]] and [[B]]. */
      def choice[A, B]: Signaling.Negative[A |&| B] =
        new Signaling.Negative[A |&| B] {
          override def signalNegFst: (Need |*| (A |&| B)) -⚬ (A |&| B) =
            dsl.signalChoice[A, B]
        }

      def rec[F[_]](implicit F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        new Negative[Rec[F]] {
          override def signalNegFst: (Need |*| Rec[F]) -⚬ Rec[F] =
            id                                     [ Need |*|   Rec[F]  ]
              .>.snd(unpack[F])                 .to[ Need |*| F[Rec[F]] ]
              .andThen(F[Rec[F]].signalNegFst)  .to[          F[Rec[F]] ]
              .pack[F]                          .to[            Rec[F]  ]
        }
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
      def law_positiveSignalThenAwaitIsId: Equal[A -⚬ A] =
        Equal[A -⚬ A](
          signalPos >>> awaitPos,
          id[A],
        )
    }

    /** Witnesses that [[A]] can both produce and await a negative (i.e. [[Need]]) signal. */
    trait Negative[A] extends Signaling.Negative[A] with Junction.Negative[A] {
      def law_negativeAwaitThenSignalIsId: Equal[A -⚬ A] =
        Equal[A -⚬ A](
          awaitNeg >>> signalNeg,
          id[A],
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

      /** Signals as soon as the `|+|` is decided, delegates awaiting to the respective side. */
      def eitherPos[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Positive[A |+| B] =
        Positive.from(
          Signaling.Positive.either[A, B],
          Junction.Positive.eitherInstance[A, B],
        )

      /** Signals as soon as the `|+|` is decided, delegates awaiting to the respective side,
        * which awaits inversion of the signal.
        */
      def eitherNeg[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Positive[A |+| B] =
        Positive.from(
          Signaling.Positive.either[A, B],
          Junction.Positive.eitherInstance(
            Junction.invert(A),
            Junction.invert(B),
          ),
        )

      def rec[F[_]](implicit F: ∀[λ[x => Positive[F[x]]]]): Positive[Rec[F]] =
        Positive.from(
          Signaling.Positive.rec(F),
          Junction.Positive.rec(F),
        )
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

      /** Signals as soon as the choice (`|&|`) is made, delegates awaiting to the chosen side. */
      def choiceNeg[A, B](implicit A: Junction.Negative[A], B: Junction.Negative[B]): Negative[A |&| B] =
        Negative.from(
          Signaling.Negative.choice[A, B],
          Junction.Negative.choiceInstance[A, B],
        )

      /** Signals as soon as the choice (`|&|`) is made, delegates awaiting to the chosen side,
        * which awaits inversion of the signal.
        */
      def choicePos[A, B](implicit A: Junction.Positive[A], B: Junction.Positive[B]): Negative[A |&| B] =
        Negative.from(
          Signaling.Negative.choice[A, B],
          Junction.Negative.choiceInstance(
            Junction.invert(A),
            Junction.invert(B),
          ),
        )

      def rec[F[_]](implicit F: ∀[λ[x => Negative[F[x]]]]): Negative[Rec[F]] =
        Negative.from(
          Signaling.Negative.rec(F),
          Junction.Negative.rec(F),
        )
    }
  }

  def race[A, B](implicit
    A: SignalingJunction.Positive[A],
    B: SignalingJunction.Positive[B],
  ): (A |*| B) -⚬ ((A |*| B) |+| (A |*| B)) =
    id                                               [                   A  |*|           B          ]
      .par(A.signalPos, B.signalPos)              .to[         (Done |*| A) |*| (Done |*| B)         ]
      .andThen(IXI)                               .to[         (Done |*| Done) |*| (A |*| B)         ]
      .>.fst(raceCompletion)                      .to[         (Done |+| Done) |*| (A |*| B)         ]
      .distributeRL                               .to[ (Done |*| (A |*| B)) |+| (Done |*| (A |*| B)) ]
      .>.left(XI.>.snd(B.awaitPos))               .to[           (A |*| B)  |+| (Done |*| (A |*| B)) ]
      .>.right(|*|.assocRL.>.fst(A.awaitPos))     .to[           (A |*| B) |+|            (A |*| B)  ]

  def race[A: SignalingJunction.Positive, B: SignalingJunction.Positive, C](
    caseFstWins: (A |*| B) -⚬ C,
    caseSndWins: (A |*| B) -⚬ C,
  ): (A |*| B) -⚬ C =
    race[A, B] >>> either(caseFstWins, caseSndWins)

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
      .andThen(IXI)                   .to[         (Need |*| A) |*| (Need |*| B)         ]
      .par(A.signalNeg, B.signalNeg)  .to[                   A  |*|           B          ]

  def select[Z, A: SignalingJunction.Negative, B: SignalingJunction.Negative](
    caseFstWins: Z -⚬ (A |*| B),
    caseSndWins: Z -⚬ (A |*| B),
  ): Z -⚬ (A |*| B) =
    choice(caseFstWins, caseSndWins) >>> select[A, B]

  def raceSignaledOrNot[A](implicit A: SignalingJunction.Positive[A]): A -⚬ (A |+| A) =
    id                                           [  A                             ]
      .andThen(A.signalPosSnd)                .to[  A |*|  Done                   ]
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
      .andThen(A.signalNegSnd)                .to[  A                             ]

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
            .andThen(f)
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
      either(f andThen injectL, g andThen injectR)
      
    def swap[A, B]: (A |+| B) -⚬ (B |+| A) =
      either(injectR, injectL)

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
      choice(chooseL andThen f, chooseR andThen g)
      
    def swap[A, B]: (A |&| B) -⚬ (B |&| A) =
      choice(chooseR, chooseL)

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

    def andThen[C](g: B -⚬ C): A -⚬ C = dsl.andThen(self, g)
    
    def after[Z](g: Z -⚬ A): Z -⚬ B = dsl.andThen(g, self)

    def bimap[F[_, _]]: BimapSyntax[F, A, B] =
      new BimapSyntax[F, A, B](self)

    /** Alias for [[andThen]]. */
    def >>>[C](g: B -⚬ C): A -⚬ C = this andThen g

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
    def > : FocusedFunctionOutputCo[A, Id, B] =
      new FocusedFunctionOutputCo[A, Id, B](self)(idFunctor)
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
  class FocusedFunctionOutputCo[A, F[_], B](f: A -⚬ F[B])(F: Functor[F]) {
    def map[C](g: B -⚬ C): A -⚬ F[C] = f andThen F.lift(g)

    /** Alias for [[map]]. */
    def apply[C](g: B -⚬ C): A -⚬ F[C] = map(g)

    def subst[C](implicit ev: B =:= C): A -⚬ F[C] =
      ev.liftCo[F].substituteCo(f)

    def unsubst[C](implicit ev: C =:= B): A -⚬ F[C] =
      ev.liftCo[F].substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(implicit ev: B =:= G[C]): FocusedFunctionOutputCo[A, λ[x => F[G[x]]], C] =
      new FocusedFunctionOutputCo[A, λ[x => F[G[x]]], C](ev.liftCo[F].substituteCo(f))(F ⚬ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(implicit ev: B =:= G[C]): FocusedFunctionOutputContra[A, λ[x => F[G[x]]], C] =
      new FocusedFunctionOutputContra[A, λ[x => F[G[x]]], C](ev.liftCo[F].substituteCo(f))(F ⚬ G)

    def co[G[_]](implicit G: Functor[G], U: Unapply[B, G]): FocusedFunctionOutputCo[A, λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(U.ev)

    def contra[G[_]](implicit G: ContraFunctor[G], U: Unapply[B, G]): FocusedFunctionOutputContra[A, λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(U.ev)

    def bi[G[_, _]](implicit G: Bifunctor[G], U: Unapply2[B, G]): FocusedFunctionOutputBi[A, λ[(x, y) => F[G[x, y]]], U.A, U.B] =
      new FocusedFunctionOutputBi[A, λ[(x, y) => F[G[x, y]]], U.A, U.B](U.ev.liftCo[F].substituteCo(f))(G inside F)

    def injectL[C]: A -⚬ F[B |+| C] = f andThen F.lift(dsl.injectL)
    def injectR[C]: A -⚬ F[C |+| B] = f andThen F.lift(dsl.injectR)
  }

  class FocusedFunctionOutputBi[A, F[_, _], B1, B2](f: A -⚬ F[B1, B2])(F: Bifunctor[F]) {
    def fst: FocusedFunctionOutputCo[A, F[*, B2], B1] =
      new FocusedFunctionOutputCo[A, F[*, B2], B1](f)(F.fst)

    def snd: FocusedFunctionOutputCo[A, F[B1, *], B2] =
      new FocusedFunctionOutputCo[A, F[B1, *], B2](f)(F.snd)
  }

  implicit class FocusedFunctionOutputOnTimesCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 |*| B2]) {
    def fst: FocusedFunctionOutputCo[A, λ[x => F[x |*| B2]], B1] =
      f.zoomCo(|*|.fst[B2])

    def snd: FocusedFunctionOutputCo[A, λ[x => F[B1 |*| x]], B2] =
      f.zoomCo(|*|.snd[B1])

    def assocLR[X, Y](implicit ev: B1 =:= (X |*| Y)): A -⚬ F[X |*| (Y |*| B2)] = {
      val g: FocusedFunctionOutputCo[A, F, (X |*| Y) |*| B2] =
        ev.substituteCo[λ[x => FocusedFunctionOutputCo[A, F, x |*| B2]]](f)
      g(|*|.assocLR)
    }

    def assocRL[X, Y](implicit ev: B2 =:= (X |*| Y)): A -⚬ F[(B1 |*| X) |*| Y] = {
      val g: FocusedFunctionOutputCo[A, F, B1 |*| (X |*| Y)] =
        ev.substituteCo[λ[x => FocusedFunctionOutputCo[A, F, B1 |*| x]]](f)
      g(|*|.assocRL)
    }

    def joinL(neglect: B1 -⚬ Done)(implicit j: Junction.Positive[B2]): A -⚬ F[B2] =
      f(par(neglect, id[B2]) >>> j.awaitPosFst)

    def joinR(neglect: B2 -⚬ Done)(implicit j: Junction.Positive[B1]): A -⚬ F[B1] =
      f(par(id[B1], neglect) >>> j.awaitPosSnd)
  }

  implicit class FocusedFunctionOutputOnDoneTimesCo[A, F[_], B2](f: FocusedFunctionOutputCo[A, F, Done |*| B2])(implicit j: Junction.Positive[B2]) {
    def joinL: A -⚬ F[B2] = f(j.awaitPosFst)
  }

  implicit class FocusedFunctionOutputOnTimesDoneCo[A, F[_], B1](f: FocusedFunctionOutputCo[A, F, B1 |*| Done])(implicit j: Junction.Positive[B1]) {
    def joinR: A -⚬ F[B1] = f(j.awaitPosSnd)
  }

  implicit class FocusedFunctionOutputOnPlusCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 |+| B2]) {
    def left: FocusedFunctionOutputCo[A, λ[x => F[x |+| B2]], B1] =
      f.zoomCo(|+|.left[B2])

    def right: FocusedFunctionOutputCo[A, λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(|+|.right[B1])

    def assocLR[X, Y](implicit ev: B1 =:= (X |+| Y)): A -⚬ F[X |+| (Y |+| B2)] = {
      val g: FocusedFunctionOutputCo[A, F, (X |+| Y) |+| B2] =
        ev.substituteCo[λ[x => FocusedFunctionOutputCo[A, F, x |+| B2]]](f)
      g(|+|.assocLR)
    }

    def assocRL[X, Y](implicit ev: B2 =:= (X |+| Y)): A -⚬ F[(B1 |+| X) |+| Y] = {
      val g: FocusedFunctionOutputCo[A, F, B1 |+| (X |+| Y)] =
        ev.substituteCo[λ[x => FocusedFunctionOutputCo[A, F, B1 |+| x]]](f)
      g(|+|.assocRL)
    }
  }

  implicit class FocusedFunctionOutputOnChoiceCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 |&| B2]) {
    def choiceL: FocusedFunctionOutputCo[A, λ[x => F[x |&| B2]], B1] =
      f.zoomCo(|&|.left[B2])

    def choiceR: FocusedFunctionOutputCo[A, λ[x => F[B1 |&| x]], B2] =
      f.zoomCo(|&|.right[B1])

    def assocLR[X, Y](implicit ev: B1 =:= (X |&| Y)): A -⚬ F[X |&| (Y |&| B2)] = {
      val g: FocusedFunctionOutputCo[A, F, (X |&| Y) |&| B2] =
        ev.substituteCo[λ[x => FocusedFunctionOutputCo[A, F, x |&| B2]]](f)
      g(|&|.assocLR)
    }

    def assocRL[X, Y](implicit ev: B2 =:= (X |&| Y)): A -⚬ F[(B1 |&| X) |&| Y] = {
      val g: FocusedFunctionOutputCo[A, F, B1 |&| (X |&| Y)] =
        ev.substituteCo[λ[x => FocusedFunctionOutputCo[A, F, B1 |&| x]]](f)
      g(|&|.assocRL)
    }
  }

  /** Focused on `B` in the output `F[B]` of linear function `A -⚬ F[B]`, where `B` is in a contravariant position. */
  class FocusedFunctionOutputContra[A, F[_], B](f: A -⚬ F[B])(F: ContraFunctor[F]) {
    def unapply[B0](g: B0 -⚬ B): A -⚬ F[B0] = f andThen F.lift(g)

    def subst[C](implicit ev: B =:= C): A -⚬ F[C] =
      ev.liftCo[F].substituteCo(f)

    def unsubst[C](implicit ev: C =:= B): A -⚬ F[C] =
      ev.liftCo[F].substituteContra(f)

    def zoomCo[G[_], C](G: Functor[G])(implicit ev: B =:= G[C]): FocusedFunctionOutputContra[A, λ[x => F[G[x]]], C] =
      new FocusedFunctionOutputContra[A, λ[x => F[G[x]]], C](ev.liftCo[F].substituteCo(f))(F ⚬ G)

    def zoomContra[G[_], C](G: ContraFunctor[G])(implicit ev: B =:= G[C]): FocusedFunctionOutputCo[A, λ[x => F[G[x]]], C] =
      new FocusedFunctionOutputCo[A, λ[x => F[G[x]]], C](ev.liftCo[F].substituteCo(f))(F ⚬ G)

    def co[G[_]](implicit G: Functor[G], U: Unapply[B, G]): FocusedFunctionOutputContra[A, λ[x => F[G[x]]], U.A] =
      zoomCo[G, U.A](G)(U.ev)

    def contra[G[_]](implicit G: ContraFunctor[G], U: Unapply[B, G]): FocusedFunctionOutputCo[A, λ[x => F[G[x]]], U.A] =
      zoomContra[G, U.A](G)(U.ev)
  }

  implicit class FocusedFunctionOutputOnTimesContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 |*| B2]) {
    def fst: FocusedFunctionOutputContra[A, λ[x => F[x |*| B2]], B1] =
      f.zoomCo(|*|.fst[B2])

    def snd: FocusedFunctionOutputContra[A, λ[x => F[B1 |*| x]], B2] =
      f.zoomCo(|*|.snd[B1])
  }

  implicit class FocusedFunctionOutputOnPlusContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 |+| B2]) {
    def left: FocusedFunctionOutputContra[A, λ[x => F[x |+| B2]], B1] =
      f.zoomCo(|+|.left[B2])

    def right: FocusedFunctionOutputContra[A, λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(|+|.right[B1])
  }

  implicit class FocusedFunctionOutputOnChoiceContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 |&| B2]) {
    def choiceL: FocusedFunctionOutputContra[A, λ[x => F[x |&| B2]], B1] =
      f.zoomCo(|&|.left[B2])

    def choiceR: FocusedFunctionOutputContra[A, λ[x => F[B1 |&| x]], B2] =
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

  def injectLWhenNeed[A, B]: A -⚬ (Need |*| ((Done |*| A) |+| B)) = {
    id                                         [                     A         ]
      .introFst(lInvertSignal).assocLR      .to[ Need |*|  (Done |*| A)        ]
      .>.snd(injectLWhenDone)               .to[ Need |*| ((Done |*| A) |+| B) ]
  }

  def injectRWhenNeed[A, B]: B -⚬ (Need |*| (A |+| (Done |*| B))) =
    id                                         [                           B   ]
      .introFst(lInvertSignal).assocLR      .to[ Need |*|        (Done |*| B)  ]
      .>.snd(injectRWhenDone)               .to[ Need |*| (A |+| (Done |*| B)) ]

  def delayEitherUntilDone[A, B]: (Done |*| (A |+| B)) -⚬ ((Done |*| A) |+| (Done |*| B)) =
    id                                                               [  Done |*| (A  |+|           B) ]
      .distributeLR                                               .to[ (Done |*|  A) |+| (Done |*| B) ]
      .either(injectLWhenDone, injectRWhenDone)                   .to[ (Done |*|  A) |+| (Done |*| B) ]

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
      .andThen(IXI)
      .>.fst(pred)
      .andThen(ifThenElse(awaitL, awaitL))
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
            .andThen(IXI)           .to[ (A    |*| S) |*| (B    |*| T) ]
            .>.fst.fst(A.counit)    .to[ (Done |*| S) |*| (B    |*| T) ]
            .>.snd.fst(B.counit)    .to[ (Done |*| S) |*| (Done |*| T) ]
            .par(f.joinL, g.joinL)  .to[           S  |*|           T  ]
        
        override def compare: (S |*| T) -⚬ Compared[S, T] = {
          id[ S |*| T ]
            .par(f.getL, g.getL)
            .andThen(IXI)
            .>.fst(self.compare)
            .andThen(Compared.enrichWith(absorb))
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
      .andThen(IXI)                           .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
      .andThen(parToOne(rInvertA, rInvertB))  .to[           One           ]

  def lInvertTimes[A, B, Ȧ, Ḃ](
    lInvertA: One -⚬ (Ȧ |*| A),
    lInvertB: One -⚬ (Ḃ |*| B),
  ): One -⚬ ((Ȧ |*| Ḃ) |*| (A |*| B)) =
    id[One]                                   .to[           One           ]
      .andThen(parFromOne(id, id))            .to[    One    |*|    One    ]
      .par(lInvertA, lInvertB)                .to[ (Ȧ |*| A) |*| (Ḃ |*| B) ]
      .andThen(IXI)                           .to[ (Ȧ |*| Ḃ) |*| (A |*| B) ]

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
      .andThen(matchingChoiceLR)    .to[ (A |*| Ȧ) |+| (B |*| Ḃ) ]
      .either(rInvertA, rInvertB)   .to[           One           ]

  def lInvertChoice[A, B, Ȧ, Ḃ](
    lInvertA: One -⚬ (Ȧ |*| A),
    lInvertB: One -⚬ (Ḃ |*| B),
  ): One -⚬ ((Ȧ |&| Ḃ) |*| (A |+| B)) =
    id                                 [           One           ]
      .choice(lInvertA, lInvertB)   .to[ (Ȧ |*| A) |&| (Ḃ |*| B) ]
      .andThen(subordinateSnd)      .to[ (Ȧ |&| Ḃ) |*| (A |+| B) ]

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
    introSnd[One] andThen par(f, g)

  def parToOne[A, B](f: A -⚬ One, g: B -⚬ One): (A |*| B) -⚬ One =
    par(f, g) andThen elimSnd[One]

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
      unpack[MultipleF[A, *]] andThen either(case0, either(case1, caseN))

    def flatten[A]: Multiple[Multiple[A]] -⚬ Multiple[A] = rec { self =>
      switch(
        case0 = zero,
        case1 = id,
        caseN = par(self, self) andThen append
      )
    }
  }

  type UnlimitedF[A, X] = One |&| (A |&| (X |*| X))

  /** Unlimited supply of `A`s. The consumer chooses how many `A`s to consume. */
  type Unlimited[A] = Rec[UnlimitedF[A, *]]
  object Unlimited {
    def discard[A]: Unlimited[A] -⚬ One =
      unpack[UnlimitedF[A, *]] andThen chooseL

    def single[A]: Unlimited[A] -⚬ A =
      unpack[UnlimitedF[A, *]] andThen chooseR andThen chooseL

    def double[A]: Unlimited[A] -⚬ (Unlimited[A] |*| Unlimited[A]) =
      unpack[UnlimitedF[A, *]] andThen chooseR andThen chooseR

    def create[X, A](
      case0: X -⚬ One,
      case1: X -⚬ A,
      caseN: X -⚬ (Unlimited[A] |*| Unlimited[A]),
    ): X -⚬ Unlimited[A] =
      choice(case0, choice(case1, caseN)) andThen pack[UnlimitedF[A, *]]

    def duplicate[A]: Unlimited[A] -⚬ Unlimited[Unlimited[A]] = rec { self =>
      create(
        case0 = discard,
        case1 = id,
        caseN = double andThen par(self, self)
      )
    }
  }

  type PUnlimitedF[A, X] = Done |&| (A |&| (X |*| X))
  type PUnlimited[A] = Rec[PUnlimitedF[A, *]]
  object PUnlimited {
    def neglect[A]: PUnlimited[A] -⚬ Done =
      unpack[PUnlimitedF[A, *]] andThen chooseL

    def single[A]: PUnlimited[A] -⚬ A =
      unpack[PUnlimitedF[A, *]] andThen chooseR andThen chooseL

    def double[A]: PUnlimited[A] -⚬ (PUnlimited[A] |*| PUnlimited[A]) =
      unpack[PUnlimitedF[A, *]] andThen chooseR andThen chooseR

    def create[X, A](
      case0: X -⚬ Done,
      case1: X -⚬ A,
      caseN: X -⚬ (PUnlimited[A] |*| PUnlimited[A]),
    ): X -⚬ PUnlimited[A] =
      choice(case0, choice(case1, caseN)) andThen pack[PUnlimitedF[A, *]]

    def duplicate[A]: PUnlimited[A] -⚬ PUnlimited[PUnlimited[A]] = rec { self =>
      create(
        case0 = neglect,
        case1 = id,
        caseN = double andThen par(self, self)
      )
    }
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

  trait Comonoid[A] extends Cosemigroup[A] {
    def counit: A -⚬ One

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
  trait NComonoid[A] extends Cosemigroup[A] {
    def counit: A -⚬ Need

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

    def law_leftUnit: Equal[ (Need |*| A) -⚬ A ] =
      Equal(
        par(regressInfinitely >>> unit, id[A]) >>> combine,
        id[Need |*| A].elimFst(regressInfinitely >>> need),
      )

    def law_rightUnit: Equal[ (A |*| Need) -⚬ A ] =
      Equal(
        par(id[A], regressInfinitely >>> unit) >>> combine,
        id[A |*| Need].elimSnd(regressInfinitely >>> need),
      )
  }

  /** A weaker version of [[Comonoid]] whose [[counit]] cannot discard the input completely, but can reduce it to
    * a signal traveling in the '''P'''ositive direction ([[Done]]) that eventually needs to be awaited.
    *
    * The dual of [[NMonoid]].
    */
  trait PComonoid[A] extends Cosemigroup[A] {
    def counit: A -⚬ Done

    def law_leftCounit: Equal[ A -⚬ (Done |*| A) ] =
      Equal(
        split >>> par(counit >>> delayIndefinitely, id[A]),
        id[A].introFst(done >>> delayIndefinitely),
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| Done) ] =
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
  
    def map[T, U](f: T -⚬ U): LList[T] -⚬ LList[U] =
      rec { self =>
        switch(nil[U], par(f, self) >>> cons)
      }
  
    def consMaybe[T]: (Maybe[T] |*| LList[T]) -⚬ LList[T] =
      id[Maybe[T] |*| LList[T]]             .to[ (One |+|                T) |*| LList[T] ]
        .distributeRL                       .to[ (One |*| LList[T]) |+| (T |*| LList[T]) ]
        .andThen(either(elimFst, cons))     .to[                 LList[T]                ]
  
    def collect[T, U](f: T -⚬ Maybe[U]): LList[T] -⚬ LList[U] =
      rec { self =>
        switch(nil[U], par(f, self) >>> consMaybe)
      }
  
    def transform[T, A, U](f: (A |*| T) -⚬ U)(implicit A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
      rec { self =>
        id                                   [  A |*|      LList[T]                             ]
          .>.snd(uncons)                  .to[  A |*| (One |+|                (T |*| LList[T])) ]
          .distributeLR                   .to[ (A |*| One) |+| (    A     |*| (T |*| LList[T])) ]
          .>.left(discardFst)             .to[        One  |+| (    A     |*| (T |*| LList[T])) ]
          .>.right.fst(A.split)           .to[        One  |+| ((A |*| A) |*| (T |*| LList[T])) ]
          .>.right(IXI)                   .to[        One  |+| ((A |*| T) |*| (A |*| LList[T])) ]
          .>.right(par(f, self))          .to[        One  |+| (    U     |*|    LList[U]     ) ]
          .either(nil[U], cons[U])        .to[            LList[U]                              ]
      }
  
    def transformCollect[T, A, U](f: (A |*| T) -⚬ Maybe[U])(implicit A: Comonoid[A]): (A |*| LList[T]) -⚬ LList[U] =
      rec { self =>
        id                                   [  A |*|      LList[T]                             ]
          .>.snd(uncons)                  .to[  A |*| (One |+|                (T |*| LList[T])) ]
          .distributeLR                   .to[ (A |*| One) |+| (    A     |*| (T |*| LList[T])) ]
          .>.left(discardFst)             .to[        One  |+| (    A     |*| (T |*| LList[T])) ]
          .>.right.fst(A.split)           .to[        One  |+| ((A |*| A) |*| (T |*| LList[T])) ]
          .>.right(IXI)                   .to[        One  |+| ((A |*| T) |*| (A |*| LList[T])) ]
          .>.right(par(f, self))          .to[        One  |+| ( Maybe[U] |*|    LList[U]     ) ]
          .either(nil[U], consMaybe[U])   .to[            LList[U]                              ]
      }
  
    def unzip[A, B]: LList[A |*| B] -⚬ (LList[A] |*| LList[B]) = rec { self =>
      val caseNil: One -⚬ (LList[A] |*| LList[B]) =
        parFromOne(nil[A], nil[B])
  
      val caseCons: ((A |*| B) |*| LList[A |*| B]) -⚬ (LList[A] |*| LList[B]) =
        par(id, self) >>> IXI >>> par(cons, cons)
  
      switch(caseNil, caseCons)
    }
  }
}
