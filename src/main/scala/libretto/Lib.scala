package libretto

class Lib(val dsl: DSL) { lib =>
  import dsl._

  /** Convenience method to summon implicit instances of [[dsl.Dual]]. */
  def Dual[A, B](implicit ev: Dual[A, B]): Dual[A, B] = ev

  /** Witnesses that `F` is a covariant endofunctor on the category `-⚬`. */
  trait CoFunctor[F[_]] { self =>
    def lift[A, B](f: A -⚬ B): F[A] -⚬ F[B]

    /** Composition with another covariant functor. */
    def ⚬[G[_]](that: CoFunctor[G]): CoFunctor[λ[x => F[G[x]]]] = new CoFunctor[λ[x => F[G[x]]]] {
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
    def ⚬[G[_]](that: CoFunctor[G]): ContraFunctor[λ[x => F[G[x]]]] = new ContraFunctor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[B]] -⚬ F[G[A]] = self.lift(that.lift(f))
    }

    /** Composition with another contravariant functor. Results in a covariant functor. */
    def ⚬[G[_]](that: ContraFunctor[G]): CoFunctor[λ[x => F[G[x]]]] = new CoFunctor[λ[x => F[G[x]]]] {
      def lift[A, B](f: A -⚬ B): F[G[A]] -⚬ F[G[B]] = self.lift(that.lift(f))
    }
  }

  def liftFst[A, B, C](f: A -⚬ C): (A |*| B) -⚬ (C |*| B) = par(f, id)
  def liftSnd[A, B, C](f: B -⚬ C): (A |*| B) -⚬ (A |*| C) = par(id, f)

  def liftL[A, B, C](f: A -⚬ C): (A |+| B) -⚬ (C |+| B) = either(f andThen injectL, injectR)
  def liftR[A, B, C](f: B -⚬ C): (A |+| B) -⚬ (A |+| C) = either(injectL, f andThen injectR)

  type Id[A] = A

  val idFunctor: CoFunctor[Id] = new CoFunctor[Id] {
    def lift[A, B](f: A -⚬ B): Id[A] -⚬ Id[B] = f
  }

  /** Product is covariant in the first argument. */
  def fst[B]: CoFunctor[* |*| B] = new CoFunctor[* |*| B] {
    def lift[A1, A2](f: A1 -⚬ A2): (A1 |*| B) -⚬ (A2 |*| B) = liftFst(f)
  }

  /** Product is covariant in the second argument. */
  def snd[A]: CoFunctor[A |*| *] = new CoFunctor[A |*| *] {
    def lift[B1, B2](f: B1 -⚬ B2): (A |*| B1) -⚬ (A |*| B2) = liftSnd(f)
  }

  /** Disjoint union is covariant in the left argument. */
  def left[B]: CoFunctor[* |+| B] = new CoFunctor[* |+| B] {
    def lift[A1, A2](f: A1 -⚬ A2): (A1 |+| B) -⚬ (A2 |+| B) = liftL(f)
  }

  /** Disjoint union is covariant in the right argument. */
  def right[A]: CoFunctor[A |+| *] = new CoFunctor[A |+| *] {
    def lift[B1, B2](f: B1 -⚬ B2): (A |+| B1) -⚬ (A |+| B2) = liftR(f)
  }

  /** Choice is covariant in the left argument. */
  def choiceL[B]: CoFunctor[* |&| B] = new CoFunctor[* |&| B] {
    def lift[A1, A2](f: A1 -⚬ A2): (A1 |&| B) -⚬ (A2 |&| B) = choice[A1 |&| B, A2, B](chooseL andThen f, chooseR)
  }

  /** Choice is covariant in the right argument. */
  def choiceR[A]: CoFunctor[A |&| *] = new CoFunctor[A |&| *] {
    def lift[B1, B2](f: B1 -⚬ B2): (A |&| B1) -⚬ (A |&| B2) = choice[A |&| B1, A, B2](chooseL, chooseR andThen f)
  }

  /** Function object (exponential) is contravariant in the input type. */
  def input[C]: ContraFunctor[* =⚬ C] = new ContraFunctor[* =⚬ C] {
    def lift[A, B](f: A -⚬ B): (B =⚬ C) -⚬ (A =⚬ C) =
      id                       [(B =⚬ C) |*| A]
        .in.snd.map(f)      .to[(B =⚬ C) |*| B]
        .andThen(eval)      .to[C]
        .as[((B =⚬ C) |*| A) -⚬ C]
        .curry
  }

  /** Function object (exponential) is covariant in the output type. */
  def output[A]: CoFunctor[A =⚬ *] = new CoFunctor[A =⚬ *] {
    def lift[B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
      id                       [(A =⚬ B) |*| A]
        .andThen(eval)      .to[B]
        .andThen(f)         .to[C]
        .as[((A =⚬ B) |*| A) -⚬ C]
        .curry
  }

  implicit class LinearFunctionOps[A, B](self: A -⚬ B) {
    /** No-op used for documentation purposes: explicitly states the input type of this linear function. */
    def from[Z](implicit ev: A =:= Z): Z -⚬ B = ev.substituteCo[* -⚬ B](self)

    /** No-op used for documentation purposes: explicitly states the output type of this linear function. */
    def to[C](implicit ev: B =:= C): A -⚬ C = ev.substituteCo(self)

    /** No-op used for documentation purposes: explicitly states the full type of this linear function. */
    def as[C](implicit ev: (A -⚬ B) =:= C): C = ev(self)

    def andThen[C](g: B -⚬ C): A -⚬ C = dsl.andThen(self, g)

    def injectL[C]: A -⚬ (B |+| C) = dsl.andThen(self, dsl.injectL)
    def injectR[C]: A -⚬ (C |+| B) = dsl.andThen(self, dsl.injectR)

    def curry[A1, A2](implicit ev: A =:= (A1 |*| A2)): A1 -⚬ (A2 =⚬ B) = dsl.curry(ev.substituteCo[* -⚬ B](self))
    def uncurry[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): (A |*| B1) -⚬ B2 = dsl.uncurry(ev.substituteCo(self))

    def in: FocusedFunctionOutputCo[A, Id, B] = new FocusedFunctionOutputCo[A, Id, B](self)(idFunctor)
  }

  /** Focused on `B` in the output `F[B]` of linear function `A -⚬ F[B]`, where `B` is in a covariant position. */
  class FocusedFunctionOutputCo[A, F[_], B](f: A -⚬ F[B])(F: CoFunctor[F]) {
    def map[C](g: B -⚬ C): A -⚬ F[C] = f andThen F.lift(g)

    def injectL[C]: A -⚬ F[B |+| C] = f andThen F.lift(dsl.injectL)
    def injectR[C]: A -⚬ F[C |+| B] = f andThen F.lift(dsl.injectR)

    def fst[B1, B2](implicit ev: B =:= (B1 |*| B2)): FocusedFunctionOutputCo[A, λ[x => F[x |*| B2]], B1] =
      new FocusedFunctionOutputCo[A, λ[x => F[x |*| B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.fst[B2])

    def snd[B1, B2](implicit ev: B =:= (B1 |*| B2)): FocusedFunctionOutputCo[A, λ[x => F[B1 |*| x]], B2] =
      new FocusedFunctionOutputCo[A, λ[x => F[B1 |*| x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.snd[B1])

    def left[B1, B2](implicit ev: B =:= (B1 |+| B2)): FocusedFunctionOutputCo[A, λ[x => F[x |+| B2]], B1] =
      new FocusedFunctionOutputCo[A, λ[x => F[x |+| B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.left[B2])

    def right[B1, B2](implicit ev: B =:= (B1 |+| B2)): FocusedFunctionOutputCo[A, λ[x => F[B1 |+| x]], B2] =
      new FocusedFunctionOutputCo[A, λ[x => F[B1 |+| x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.right[B1])

    def choiceL[B1, B2](implicit ev: B =:= (B1 |&| B2)): FocusedFunctionOutputCo[A, λ[x => F[x |&| B2]], B1] =
      new FocusedFunctionOutputCo[A, λ[x => F[x |&| B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.choiceL[B2])

    def choiceR[B1, B2](implicit ev: B =:= (B1 |&| B2)): FocusedFunctionOutputCo[A, λ[x => F[B1 |&| x]], B2] =
      new FocusedFunctionOutputCo[A, λ[x => F[B1 |&| x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.choiceR[B1])

    def input[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): FocusedFunctionOutputContra[A, λ[x => F[x =⚬ B2]], B1] =
      new FocusedFunctionOutputContra[A, λ[x => F[x =⚬ B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.input[B2])

    def output[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): FocusedFunctionOutputCo[A, λ[x => F[B1 =⚬ x]], B2] =
      new FocusedFunctionOutputCo[A, λ[x => F[B1 =⚬ x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.output[B1])
  }

  /** Focused on `B` in the output `F[B]` of linear function `A -⚬ F[B]`, where `B` is in a contravariant position. */
  class FocusedFunctionOutputContra[A, F[_], B](f: A -⚬ F[B])(F: ContraFunctor[F]) {
    def contramap[B0](g: B0 -⚬ B): A -⚬ F[B0] = f andThen F.lift(g)

    def fst[B1, B2](implicit ev: B =:= (B1 |*| B2)): FocusedFunctionOutputContra[A, λ[x => F[x |*| B2]], B1] =
      new FocusedFunctionOutputContra[A, λ[x => F[x |*| B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.fst[B2])

    def snd[B1, B2](implicit ev: B =:= (B1 |*| B2)): FocusedFunctionOutputContra[A, λ[x => F[B1 |*| x]], B2] =
      new FocusedFunctionOutputContra[A, λ[x => F[B1 |*| x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.snd[B1])

    def left[B1, B2](implicit ev: B =:= (B1 |+| B2)): FocusedFunctionOutputContra[A, λ[x => F[x |+| B2]], B1] =
      new FocusedFunctionOutputContra[A, λ[x => F[x |+| B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.left[B2])

    def right[B1, B2](implicit ev: B =:= (B1 |+| B2)): FocusedFunctionOutputContra[A, λ[x => F[B1 |+| x]], B2] =
      new FocusedFunctionOutputContra[A, λ[x => F[B1 |+| x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.right[B1])

    def input[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): FocusedFunctionOutputCo[A, λ[x => F[x =⚬ B2]], B1] =
      new FocusedFunctionOutputCo[A, λ[x => F[x =⚬ B2]], B1](ev.liftCo[F].substituteCo(f))(F ⚬ lib.input[B2])

    def output[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): FocusedFunctionOutputContra[A, λ[x => F[B1 =⚬ x]], B2] =
      new FocusedFunctionOutputContra[A, λ[x => F[B1 =⚬ x]], B2](ev.liftCo[F].substituteCo(f))(F ⚬ lib.output[B1])
  }

  def IXI[A, B, C, D]: ((A|*|B)|*|(C|*|D)) -⚬
  //                     |    \   /    |
  //                     |     \ /     |
  //                     |      X      |
  //                     |     / \     |
  //                     |    /   \    |
                       ((A|*|C)|*|(B|*|D)) =
    id                             [ (A |*| B) |*| (C |*| D) ]
      .andThen(timesAssocLR)    .to[ A |*| (B |*| (C |*| D)) ]
      .in.snd.map(timesAssocRL) .to[ A |*| ((B |*| C) |*| D) ]
      .in.snd.fst.map(swap)     .to[ A |*| ((C |*| B) |*| D) ]
      .in.snd.map(timesAssocLR) .to[ A |*| (C |*| (B |*| D)) ]
      .andThen(timesAssocRL)    .to[ (A |*| C) |*| (B |*| D) ]

  /** From the choice ''available'' on the right (`C |&| D`), choose the one corresponding to the choice ''made''
    * on the left (`A |+| B`): if on the left there is `A`, choose `C`, if on the left thre is `B`, choose `D`.
    */
  def matchingChoiceLR[A, B, C, D]: ((A |+| B) |*| (C |&| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |+| B) |*| (C |&| D)]
      .andThen(distributeL)        .to[(A |*| (C |&| D)) |+| (B |*| (C |&| D))]
      .in.left.snd.map(chooseL)    .to[(A |*|  C       ) |+| (B |*| (C |&| D))]
      .in.right.snd.map(chooseR)   .to[(A |*|  C       ) |+| (B |*|        D )]

  /** From the choice ''available'' on the left (`A |&| B`), choose the one corresponding to the choice ''made''
    * on the right (`C |+| D`): if on the right there is `C`, choose `A`, if on the right there is `D`, choose `B`.
    */
  def matchingChoiceRL[A, B, C, D]: ((A |&| B) |*| (C |+| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |&| B) |*| (C |+| D)]
      .andThen(distributeR)        .to[((A |&| B) |*| C) |+| ((A |&| B) |*| D)]
      .in.left.fst.map(chooseL)    .to[( A        |*| C) |+| ((A |&| B) |*| D)]
      .in.right.fst.map(chooseR)   .to[( A        |*| C) |+| (       B  |*| D)]

  def zip[A1, A2, B1, B2]: ((A1 |*| A2) |*| (B1 |*| B2)) -⚬ ((A1 |*| B1) |*| (A2 |*| B2)) = {
    id                              [ (A1 |*|  A2) |*| (B1   |*| B2)]
      .andThen(timesAssocRL)     .to[((A1 |*|  A2) |*|  B1)  |*| B2 ]
      .in.fst.map(timesAssocLR)  .to[( A1 |*| (A2  |*|  B1)) |*| B2 ]
      .in.fst.snd.map(swap)      .to[( A1 |*| (B1  |*|  A2)) |*| B2 ]
      .in.fst.map(timesAssocRL)  .to[((A1 |*|  B1) |*|  A2)  |*| B2 ]
      .andThen(timesAssocLR)     .to[ (A1 |*|  B1) |*| (A2   |*| B2)]
    }

  def zapPremises[A, Ā, B, C](implicit ev: Dual[A, Ā]): ((A =⚬ B) |*| (Ā =⚬ C)) -⚬ (B |*| C) = {
    id                              [  (A =⚬ B) |*| (Ā =⚬ C)                ]
      .andThen(introSnd)         .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*|    One    ]
      .in.snd.map(ev.introduce)  .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (A |*| Ā) ]
      .andThen(zip)              .to[ ((A =⚬ B) |*| A) |*| ((Ā =⚬ C) |*| Ā) ]
      .andThen(par(eval, eval))  .to[        B         |*|        C         ]
  }

  def dualSymmetric[A, B](ev: Dual[A, B]): Dual[B, A] = new Dual[B, A] {
    def introduce: One -⚬ (B |*| A) = andThen(ev.introduce, swap)
    def eliminate: B |*| A -⚬ One = andThen(swap, ev.eliminate)
  }

  implicit def oneSelfDual: Dual[One, One] = new Dual[One, One] {
    def introduce: One -⚬ (One |*| One) = introSnd
    def eliminate: One |*| One -⚬ One = elimSnd
  }

  implicit def productDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |*| B, Ȧ |*| Ḃ] =
    new Dual[A |*| B, Ȧ |*| Ḃ] {
      def introduce: One -⚬ ((A |*| B) |*| (Ȧ |*| Ḃ)) = {
        id[One]                                   .to[           One           ]
          .andThen(introSnd)                      .to[    One    |*|    One    ]
          .andThen(par(a.introduce, b.introduce)) .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
          .andThen(zip)                           .to[ (A |*| B) |*| (Ȧ |*| Ḃ) ]
      }

      def eliminate: ((A |*| B) |*| (Ȧ |*| Ḃ)) -⚬ One = {
        id[(A |*| B) |*| (Ȧ |*| Ḃ)]               .to[ (A |*| B) |*| (Ȧ |*| Ḃ) ]
          .andThen(zip)                           .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
          .andThen(par(a.eliminate, b.eliminate)) .to[    One    |*|    One    ]
          .andThen(elimSnd)                       .to[           One           ]
      }
    }

  implicit def eitherChoiceDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |+| B, Ȧ |&| Ḃ] =
    dualSymmetric(choiceEitherDuality(dualSymmetric(a), dualSymmetric(b)))

  implicit def negValDuality[A]: Dual[Neg[A], Val[A]] =
    dualSymmetric(valNegDuality)

  /** Given `A` and `B` concurrently (`A |*| B`), we can mandate that `A` be consumed before `B`
    * by turning it into `Ā =⚬ B`, where `Ā` is the dual of `A`.
    */
  def unveilSequentially[A, Ā, B](implicit ev: Dual[A, Ā]): (A |*| B) -⚬ (Ā =⚬ B) =
    id[(A |*| B) |*| Ā]           .to[ (A |*|  B) |*| Ā  ]
      .andThen(timesAssocLR)      .to[  A |*| (B  |*| Ā) ]
      .in.snd.map(swap)           .to[  A |*| (Ā  |*| B) ]
      .andThen(timesAssocRL)      .to[ (A |*|  Ā) |*| B  ]
      .in.fst.map(ev.eliminate)   .to[    One     |*| B  ]
      .andThen(elimFst)           .to[                B  ]
      .as[ ((A |*| B) |*| Ā) -⚬ B ]
      .curry

  /** Make the function on the left ''"absorb"'' the value on the right and return it as part of its output. */
  def absorbR[A, B, C]: ((A =⚬ B) |*| C) -⚬ (A =⚬ (B |*| C)) =
    id[((A =⚬ B) |*| C) |*| A]  .to[ ((A =⚬ B) |*| C) |*| A ]
      .andThen(timesAssocLR)    .to[ (A =⚬ B) |*| (C |*| A) ]
      .in.snd.map(swap)         .to[ (A =⚬ B) |*| (A |*| C) ]
      .andThen(timesAssocRL)    .to[ ((A =⚬ B) |*| A) |*| C ]
      .in.fst.map(eval)         .to[        B         |*| C ]
      .as[ (((A =⚬ B) |*| C) |*| A) -⚬ (B |*| C) ]
      .curry

  def liftOption[A]: Val[Option[A]] -⚬ (One |+| Val[A]) =
    id[Val[Option[A]]]                .to[ Val[Option[      A]] ]
      .andThen(liftV(_.toRight(())))  .to[ Val[Either[Unit, A]] ]
      .andThen(liftEither)            .to[ Val[Unit] |+| Val[A] ]
      .in.left.map(discard)           .to[   One     |+| Val[A] ]

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
        .andThen(pack[MultipleF[A, *]])

    def one[A]: A -⚬ Multiple[A] =
      id[A]
        .injectL[Multiple[A] |*| Multiple[A]]
        .injectR[One]
        .andThen(pack[MultipleF[A, *]])

    def append[A]: (Multiple[A] |*| Multiple[A]) -⚬ Multiple[A] =
      id[Multiple[A] |*| Multiple[A]]
        .injectR[A]
        .injectR[One]
        .andThen(pack[MultipleF[A, *]])

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

  trait Monoid[A] {
    def unit    :       One -⚬ A
    def combine : (A |*| A) -⚬ A
  }

  trait Monad[F[_]] {
    def pure[A]    :       A -⚬ F[A]
    def flatten[A] : F[F[A]] -⚬ F[A]
  }

  trait Comonoid[A] {
    def counit : A -⚬ One
    def split  : A -⚬ (A |*| A)
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

  implicit val comonadUnlimited: Comonad[Unlimited] =
    new Comonad[Unlimited] {
      def extract[A]   : Unlimited[A] -⚬ A                       = Unlimited.single
      def duplicate[A] : Unlimited[A] -⚬ Unlimited[Unlimited[A]] = Unlimited.duplicate
    }

  type PollableF[A, X] = One |&| (One |+| (Val[A] |*| X))
  type Pollable[A] = Rec[PollableF[A, *]]
  type Polled[A] = One |+| (Val[A] |*| Pollable[A])

  type PullingF[A, X]  = One |+| (One |&| (Neg[A] |*| X))
  type Pulling[A] = Rec[PullingF[A, *]]

  type ProducingF[A, X]  = One |+| (One |&| (Val[A] |*| X))
  type Producing[A] = Rec[ProducingF[A, *]]

  type ConsumerF[A, X] = One |&| (One |+| (Neg[A] |*| X))
  type Consumer[A] = Rec[ConsumerF[A, *]]

  object Pollable {
    def close[A]: Pollable[A] -⚬ One =
      id                       [   Pollable[A]     ]
        .andThen(unpack)    .to[ One |&| Polled[A] ]
        .andThen(chooseL)   .to[ One               ]

    def poll[A]: Pollable[A] -⚬ Polled[A] =
      id                       [   Pollable[A]     ]
        .andThen(unpack)    .to[ One |&| Polled[A] ]
        .andThen(chooseR)   .to[         Polled[A] ]

    /** Polls and discards all elements. */
    def drain[A]: Pollable[A] -⚬ One = rec { self =>
      poll[A] andThen either(id, parToOne(discard, self))
    }

    def emptyF[A]: One -⚬ PollableF[A, Pollable[A]] =
      choice[One, One, Polled[A]](id, injectL)

    def empty[A]: One -⚬ Pollable[A] =
      emptyF[A] andThen pack[PollableF[A, *]]

    def fromList[A]: Val[List[A]] -⚬ Pollable[A] = rec { self =>
      val uncons: List[A] => Option[(A, List[A])] = _ match {
        case a :: as => Some((a, as))
        case Nil => None
      }

      val close: Val[List[A]] -⚬ One = discard

      val poll: Val[List[A]] -⚬ Polled[A] =
        liftV(uncons)                           .to[ Val[Option[(A, List[A])]] ]
          .andThen(liftOption)                  .to[ One |+| Val[(A, List[A])] ]
          .in.right.map(liftPair)               .to[ One |+| (Val[A] |*| Val[List[A]]) ]
          .in.right.snd.map(self)               .to[ One |+| (Val[A] |*| Pollable[A] ) ]

      choice(close, poll)
        .andThen(pack[PollableF[A, *]])
    }

    def prepend[A]: (Val[A] |*| Pollable[A]) -⚬ Pollable[A] = {
      val close: (Val[A] |*| Pollable[A]) -⚬ One =
        parToOne(discard, Pollable.close)

      val poll: (Val[A] |*| Pollable[A]) -⚬ Polled[A] =
        injectR

      choice(close, poll)
        .andThen(pack[PollableF[A, *]])
    }

    def concat[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] = rec { self =>
      val close: (Pollable[A] |*| Pollable[A]) -⚬ One =
        parToOne(Pollable.close, Pollable.close)

      val poll: (Pollable[A] |*| Pollable[A]) -⚬ Polled[A] =
        id[Pollable[A] |*| Pollable[A]] .to[                               Pollable[A]    |*| Pollable[A] ]
          .in.fst.map(unpack)           .to[ (One |&| (One |+| (Val[A] |*| Pollable[A]))) |*| Pollable[A] ]
          .in.fst.map(chooseR)          .to[          (One |+| (Val[A] |*| Pollable[A]))  |*| Pollable[A] ]
          .andThen(distributeL)         .to[ (One |*| Pollable[A])  |+| ((Val[A] |*|  Pollable[A]) |*| Pollable[A])  ]
          .in.left.map(elimFst)         .to[          Pollable[A]   |+| ((Val[A] |*|  Pollable[A]) |*| Pollable[A])  ]
          .in.left.map(Pollable.poll)   .to[           Polled[A]    |+| ((Val[A] |*|  Pollable[A]) |*| Pollable[A])  ]
          .in.right.map(timesAssocLR)   .to[           Polled[A]    |+| ( Val[A] |*| (Pollable[A]  |*| Pollable[A])) ]
          .in.right.snd.map(self)       .to[           Polled[A]    |+| ( Val[A] |*|            Pollable[A]        ) ]
          .in.right.injectR[One]        .to[           Polled[A]    |+|        Polled[A]                             ]
          .andThen(either(id, id))      .to[                     Polled[A]                                           ]

      choice(close, poll)
        .andThen(pack[PollableF[A, *]])
    }

    /** Merges two [[Pollable]]s into one. When there is a value available from both upstreams, favors the first one. */
    def merge[A]: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A] = rec { self =>
      val close: (Pollable[A] |*| Pollable[A]) -⚬ One =
        parToOne(Pollable.close, Pollable.close)

      val unpoll: Polled[A] -⚬ Pollable[A] = {
        val closePolled: Polled[A] -⚬ One =
          either(id, parToOne(discard, Pollable.close))

        choice(closePolled, id[Polled[A]])
          .andThen(pack[PollableF[A, *]])
      }

      // checks the first argument first, uses the given function for recursive calls
      def go(merge: (Pollable[A] |*| Pollable[A]) -⚬ Pollable[A]): (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        id[Polled[A] |*| Polled[A]]   .to[ (One |+| (Val[A] |*| Pollable[A])) |*| Polled[A]                   ]
          .andThen(distributeL)       .to[ (One |*| Polled[A]) |+| ((Val[A] |*| Pollable[A]) |*|  Polled[A] ) ]
          .in.left.map(elimFst)       .to[          Polled[A]  |+| ((Val[A] |*| Pollable[A]) |*|  Polled[A] ) ]
          .in.right.snd.map(unpoll)   .to[          Polled[A]  |+| ((Val[A] |*| Pollable[A]) |*| Pollable[A]) ]
          .in.right.map(timesAssocLR) .to[          Polled[A]  |+| (Val[A] |*| (Pollable[A] |*| Pollable[A])) ]
          .in.right.snd.map(merge)    .to[          Polled[A]  |+| (Val[A] |*|          Pollable[A]         ) ]
          .in.right.injectR[One]      .to[          Polled[A]  |+|       Polled[A]                            ]
          .andThen(either(id, id))    .to[                  Polled[A]                                         ]

      // checks the first argument first
      val goFst: (Polled[A] |*| Polled[A]) -⚬ Polled[A] = go(self)

      // checks the second argument first
      val goSnd: (Polled[A] |*| Polled[A]) -⚬ Polled[A] =
        swap[Polled[A], Polled[A]]
          .andThen(go(swap[Pollable[A], Pollable[A]] andThen self))

      val poll: (Pollable[A] |*| Pollable[A]) -⚬ Polled[A] =
        id[Pollable[A] |*| Pollable[A]]               .to[ Pollable[A] |*| Pollable[A]                               ]
          .andThen(par(Pollable.poll, Pollable.poll)) .to[  Polled[A]  |*|  Polled[A]                                ]
          .andThen(race)                              .to[ (Polled[A]  |*|  Polled[A]) |+| (Polled[A] |*| Polled[A]) ]
          .andThen(either(goFst, goSnd))              .to[                          Polled[A]                        ]

      choice(close, poll)
        .andThen(pack[PollableF[A, *]])
    }

    // TODO: polish
    def dup[A]: Pollable[A] -⚬ (Pollable[A] |*| Pollable[A]) = rec { self =>
      // the case when the first output polls or closes before the second output does
      val caseFst: Pollable[A] -⚬ ((One |&| Polled[A]) |*| (One |&| Polled[A])) = {
        val caseFstClosed: Pollable[A] -⚬ (One |*| (One |&| Polled[A])) =
          id[ Pollable[A] ]     .to[            Pollable[A]      ]
            .andThen(unpack)    .to[          One |&| Polled[A]  ]
            .andThen(introFst)  .to[ One |*| (One |&| Polled[A]) ]

        val caseFstPolled: Pollable[A] -⚬ (Polled[A] |*| (One |&| Polled[A])) = {
          val caseUpstreamClosed: One -⚬ (Polled[A] |*| (One |&| Polled[A])) = {
            val closedPolled: One -⚬ Polled[A] = injectL
            parFromOne(closedPolled, choice(id, closedPolled))
          }

          val caseUpstreamValue:  (Val[A] |*| Pollable[A]) -⚬ (Polled[A] |*| (One |&| Polled[A])) = {
            val goSnd: (Val[A] |*| Pollable[A]) -⚬ (Pollable[A] |*| (One |&| Polled[A])) = {
              val sndClosed: (Val[A] |*| Pollable[A]) -⚬ (Pollable[A] |*| One) =
                swap[Val[A], Pollable[A]]     .from[ Val[A] |*| Pollable[A] ]
                                              .to  [ Pollable[A] |*| Val[A] ]
                  .in.snd.map(discard)        .to  [ Pollable[A] |*|  One   ]

              val sndPolled: (Val[A] |*| Pollable[A]) -⚬ (Pollable[A] |*| Polled[A]) =
                id[ Val[A] |*| Pollable[A] ]
                  .in.snd.map(self)     .to[ Val[A] |*| (Pollable[A] |*| Pollable[A]) ]
                  .andThen(timesAssocRL).to[ (Val[A] |*| Pollable[A]) |*| Pollable[A] ]
                  .in.fst.map(swap)     .to[ (Pollable[A] |*| Val[A]) |*| Pollable[A] ]
                  .andThen(timesAssocLR).to[ Pollable[A] |*| (Val[A] |*| Pollable[A]) ]
                  .in.snd.injectR[One]  .to[ Pollable[A] |*|      Polled[A]           ]

              choice(sndClosed, sndPolled)  .from[ Val[A] |*| Pollable[A] ]
                                            .to  [ (Pollable[A] |*| One) |&| (Pollable[A] |*| Polled[A]) ]
                .andThen(coDistributeL)     .to  [ Pollable[A] |*| (One |&| Polled[A])                   ]
            }

            id                                   [        Val[A]       |*| Pollable[A]              ]
              .in.fst.map(dsl.dup)            .to[ (Val[A] |*| Val[A]) |*| Pollable[A]              ]
              .andThen(timesAssocLR)          .to[ Val[A] |*| (Val[A] |*| Pollable[A])              ]
              .in.snd.map(goSnd)              .to[ Val[A] |*| (Pollable[A] |*| (One |&| Polled[A])) ]
              .andThen(timesAssocRL)          .to[ (Val[A] |*| Pollable[A]) |*| (One |&| Polled[A]) ]
              .in.fst.injectR[One]            .to[      Polled[A]           |*| (One |&| Polled[A]) ]
          }

          Pollable.poll[A]                                          .from[          Pollable[A]              ]
                                                                    .to  [ One |+| (Val[A] |*| Pollable[A])  ]
            .andThen(either(caseUpstreamClosed, caseUpstreamValue)) .to  [ Polled[A] |*| (One |&| Polled[A]) ]
        }

        choice(caseFstClosed, caseFstPolled)  .from[                          Pollable[A]                                  ]
                                              .to  [ (One |*| (One |&| Polled[A])) |&| (Polled[A] |*| (One |&| Polled[A])) ]
          .andThen(coDistributeR)             .to  [ (One |&| Polled[A]) |*| (One |&| Polled[A])                           ]
      }

      // the case when the second output polls or closes before the first output does
      val caseSnd: Pollable[A] -⚬ ((One |&| Polled[A]) |*| (One |&| Polled[A])) =
        caseFst andThen swap

      id[Pollable[A]]                                               .to[                                           Pollable[A]                                           ]
        .andThen(choice(caseFst, caseSnd))                          .to[ ((One |&| Polled[A]) |*| (One |&| Polled[A])) |&| ((One |&| Polled[A]) |*| (One |&| Polled[A])) ]
        .andThen(select)                                            .to[                           (One |&| Polled[A]) |*| (One |&| Polled[A])                           ]
        .andThen(par(pack[PollableF[A, *]], pack[PollableF[A, *]])) .to[                              Pollable[A]      |*|    Pollable[A]                                ]
    }

    def dropUntilFirstDemand[A]: Pollable[A] -⚬ Pollable[A] = {
      val goUnpacked: (One |&| Polled[A]) -⚬ (One |&| Polled[A]) = rec { self =>
        val caseDownstreamRequested: (Val[A] |*| Pollable[A]) -⚬ (One |&| Polled[A]) = {
          val caseDownstreamClosed: (Val[A] |*| Pollable[A]) -⚬ One       = parToOne(discard, Pollable.close)
          val caseDownstreamPulled: (Val[A] |*| Pollable[A]) -⚬ Polled[A] = injectR
          choice(caseDownstreamClosed, caseDownstreamPulled)
        }

        val caseNotRequestedYet: (Val[A] |*| Pollable[A]) -⚬ (One |&| Polled[A]) = {
          id[Val[A] |*| Pollable[A]]
            .in.fst.map(discard)
            .andThen(elimFst)
            .andThen(unpack)
            .andThen(self)
        }

        val goElem: (Val[A] |*| Pollable[A]) -⚬ (One |&| Polled[A]) =
          choice(caseDownstreamRequested, caseNotRequestedYet)
            .andThen(selectRequestedOrNot)

        id                                       [ One |&| Polled[A]                ]
          .andThen(chooseR)                   .to[ One |+| (Val[A] |*| Pollable[A]) ]
          .andThen(either(emptyF[A], goElem)) .to[ One |&| Polled[A]                ]
      }

      unpack[PollableF[A, *]]
        .andThen(goUnpacked)
        .andThen(pack[PollableF[A, *]])
    }

    def broadcast[A]: Pollable[A] -⚬ Unlimited[Pollable[A]] = rec { self =>
      val case0: Pollable[A] -⚬ One                                                 = Pollable.close
      val case1: Pollable[A] -⚬ Pollable[A]                                         = id
      val caseN: Pollable[A] -⚬ (Unlimited[Pollable[A]] |*| Unlimited[Pollable[A]]) = dup andThen par(self, self)

      dropUntilFirstDemand
        .andThen(choice(case0, (choice(case1, caseN))))
        .andThen(pack[UnlimitedF[Pollable[A], *]])
    }
  }

  implicit def consumerProducingDuality[A]: Dual[Consumer[A], Producing[A]] =
    dualRec[ConsumerF[A, *], ProducingF[A, *]](
      new Dual1[ConsumerF[A, *], ProducingF[A, *]] {
        def apply[x, y]: Dual[x, y] => Dual[ConsumerF[A, x], ProducingF[A, y]] = { xy_dual =>
          choiceEitherDuality(
            Dual[One, One],
            eitherChoiceDuality(
              Dual[One, One],
              productDuality(
                Dual[Neg[A], Val[A]],
                xy_dual
              )
            )
          )
        }
      }
    )

  implicit def producingConsumerDuality[A]: Dual[Producing[A], Consumer[A]] =
    dualSymmetric(consumerProducingDuality[A])

  implicit def pullingPollableDuality[A]: Dual[Pulling[A], Pollable[A]] =
    dualRec[PullingF[A, *], PollableF[A, *]](
      new Dual1[PullingF[A, *], PollableF[A, *]] {
        def apply[x, y]: Dual[x, y] => Dual[PullingF[A, x], PollableF[A, y]] = { xy_dual =>
          eitherChoiceDuality(
            Dual[One, One],
            choiceEitherDuality(
              Dual[One, One],
              productDuality(
                Dual[Neg[A], Val[A]],
                xy_dual
              )
            )
          )
        }
      }
    )

  implicit def pollablePullingDuality[A]: Dual[Pollable[A], Pulling[A]] =
    dualSymmetric(pullingPollableDuality[A])

  /** If either the source or the sink is completed, complete the other one and be done.
    * Otherwise, expose their offer and demand, respectively.
    */
  def relayCompletion[A, B]: (Pollable[A] |*| Pulling[B]) -⚬ (One |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Pulling[B]))) =
    id                                    [ Pollable[A] |*| (                    Pulling[B]                                  )]
      .in.snd.map(unpack)              .to[ Pollable[A] |*| (One     |+|                    (One |&| (Neg[B] |*| Pulling[B])))]
      .andThen(distributeR)            .to[(Pollable[A] |*|  One)    |+| (Pollable[A]   |*| (One |&| (Neg[B] |*| Pulling[B])))]
      .in.left.map(elimSnd)            .to[ Pollable[A]              |+| (Pollable[A]   |*| (One |&| (Neg[B] |*| Pulling[B])))]
      .in.left.map(Pollable.close)     .to[ One |+|                      (Pollable[A]   |*| (One |&| (Neg[B] |*| Pulling[B])))]
      .in.right.fst.map(Pollable.poll) .to[ One |+| ((One |+| (Val[A] |*| Pollable[A])) |*| (One |&| (Neg[B] |*| Pulling[B])))]
      .in.right.map(matchingChoiceLR)  .to[ One |+| ((One |*| One) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Pulling[B])))]
      .in.right.left.map(elimSnd)      .to[ One |+| (     One      |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Pulling[B])))]
      .andThen(plusAssocRL)            .to[(One |+|       One    ) |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Pulling[B])) ]
      .in.left.map(either(id, id))     .to[     One                |+| ((Val[A] |*| Pollable[A]) |*| (Neg[B] |*| Pulling[B])) ]

  type Source[A] = One -⚬ Pollable[A]
  object Source {
    def empty[A]: Source[A] = {
      choice(id[One], injectL[One, Val[A] |*| Pollable[A]])
        .andThen(pack[PollableF[A, *]])
    }

    def singleton[A](a: A): Source[A] = {
      val poll: One -⚬ (One |+| (Val[A] |*| Pollable[A])) =
        parFromOne(const(a), Source.empty[A]) .from[                 One              ]
                                              .to  [          Val[A] |*| Pollable[A]  ]
          .injectR                            .to  [ One |+| (Val[A] |*| Pollable[A]) ]

      choice(id[One], poll)
        .andThen(pack[PollableF[A, *]])
    }

    def fromList[A](elems: List[A]): Source[A] = {
      const(elems) andThen Pollable.fromList[A]
    }

    def concat[A](src1: Source[A], src2: Source[A]): Source[A] = {
      parFromOne(src1, src2)
        .andThen(Pollable.concat[A])
    }
  }

  type Pipe[A, B] = Pollable[A] -⚬ Pollable[B]
  object Pipe {
    def lift[A, B](f: A => B): Pipe[A, B] = {
      val ff: Val[A] -⚬ Val[B] = liftV(f)

      rec(self =>
        id[Pollable[A]]                         .to[   Pollable[A]                              ]
          .andThen(unpack)                      .to[ One |&| (One |+| (Val[A] |*| Pollable[A])) ]
          .in.choiceR.right.fst.map(ff)         .to[ One |&| (One |+| (Val[B] |*| Pollable[A])) ]
          .in.choiceR.right.snd.map(self)       .to[ One |&| (One |+| (Val[B] |*| Pollable[B])) ]
          .andThen(pack[PollableF[B, *]])       .to[                              Pollable[B]   ]
      )
    }

    def statefulMap[S, A, B](f: ((S, A)) => (S, B))(initialState: S): Pipe[A, B] = {
      val ff: (Val[S] |*| Val[A]) -⚬ (Val[S] |*| Val[B]) =
        unliftPair[S, A]
          .andThen(liftV(f))
          .andThen(liftPair[S, B])

      val inner: (Val[S] |*| Pollable[A]) -⚬ Pollable[B] = rec { self =>
        val close: (Val[S] |*| Pollable[A]) -⚬ One =
          parToOne(discard, Pollable.close)

        val poll:(Val[S] |*| Pollable[A]) -⚬ (One |+| (Val[B] |*| Pollable[B])) =
          id[Val[S] |*| Pollable[A]]              .to[ Val[S] |*|                      Pollable[A]   ]
            .in.snd.map(Pollable.poll)            .to[ Val[S] |*| (One |+| (Val[A] |*| Pollable[A])) ]
            .andThen(distributeR)                 .to[ (Val[S] |*| One) |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .in.left.map(elimSnd andThen discard) .to[         One      |+| (Val[S] |*| (Val[A] |*| Pollable[A])) ]
            .in.right.map(timesAssocRL)           .to[         One      |+| ((Val[S] |*| Val[A]) |*| Pollable[A]) ]
            .in.right.fst.map(ff)                 .to[         One      |+| ((Val[S] |*| Val[B]) |*| Pollable[A]) ]
            .in.right.fst.map(swap)               .to[         One      |+| ((Val[B] |*| Val[S]) |*| Pollable[A]) ]
            .in.right.map(timesAssocLR)           .to[         One      |+| (Val[B] |*| (Val[S] |*| Pollable[A])) ]
            .in.right.snd.map(self)               .to[         One      |+| (Val[B] |*|     Pollable[B]         ) ]

        choice(close, poll)
          .andThen(pack[PollableF[B, *]])
      }

      id[Pollable[A]]                     .to[            Pollable[A] ]
        .andThen(introFst)                .to[  One   |*| Pollable[A] ]
        .in.fst.map(const(initialState))  .to[ Val[S] |*| Pollable[A] ]
        .andThen(inner)
    }
  }
}