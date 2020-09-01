package libretto

class Lib[DSL <: libretto.DSL](val dsl: DSL) { lib =>
  import dsl._

  /** Convenience method to summon implicit instances of [[dsl.Dual]]. */
  def Dual[A, B](implicit ev: Dual[A, B]): Dual[A, B] = ev

  def zap[A, B](implicit ev: Dual[A, B]): (A |*| B) -⚬ One =
    ev.eliminate

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

  trait Transportive[F[_]] extends Functor[F] {
    def inL[A, B]: (A |*| F[B]) -⚬ F[A |*| B]
    def outL[A, B]: F[A |*| B] -⚬ (A |*| F[B])

    def inR[A, B]: (F[A] |*| B) -⚬ F[A |*| B] =
      swap[F[A], B] >>> inL >>> lift(swap[B, A])

    def outR[A, B]: F[A |*| B] -⚬ (F[A] |*| B) =
      lift(swap[A, B]) >>> outL >>> swap[B, F[A]]
  }

  trait Unapply[FA, F[_]] {
    type A
    def ev: FA =:= F[A]
  }

  object Unapply {
    implicit def unapplyInstance[F[_], X]: Unapply[F[X], F] { type A = X } =
      new Unapply[F[X], F] {
        type A = X
        val ev: F[X] =:= F[A] = implicitly
      }
  }

  trait Unapply2[FAB, F[_, _]] {
    type A
    type B
    def ev: FAB =:= F[A, B]
  }

  object Unapply2 {
    implicit def unapply2Instance[F[_, _], X, Y]: Unapply2[F[X, Y], F] { type A = X; type B = Y } =
      new Unapply2[F[X, Y], F] {
        type A = X
        type B = Y
        val ev: F[X, Y] =:= F[A, B] = implicitly
      }
  }

  def liftFst[A, B, C](f: A -⚬ C): (A |*| B) -⚬ (C |*| B) = par(f, id)
  def liftSnd[A, B, C](f: B -⚬ C): (A |*| B) -⚬ (A |*| C) = par(id, f)

  def liftL[A, B, C](f: A -⚬ C): (A |+| B) -⚬ (C |+| B) = either(f andThen injectL, injectR)
  def liftR[A, B, C](f: B -⚬ C): (A |+| B) -⚬ (A |+| C) = either(injectL, f andThen injectR)

  type Id[A] = A

  implicit val idFunctor: Transportive[Id] = new Transportive[Id] {
    def lift[A, B](f: A -⚬ B): Id[A] -⚬ Id[B] = f
    def inL[A, B]: (A |*| Id[B]) -⚬ Id[A |*| B] = id
    def outL[A, B]: Id[A |*| B] -⚬ (A |*| Id[B]) = id
  }

  /** Product is covariant in the first argument. */
  implicit def fst[B]: Transportive[* |*| B] = new Transportive[* |*| B] {
    def lift[A1, A2](f: A1 -⚬ A2): (A1 |*| B) -⚬ (A2 |*| B) = liftFst(f)
    def inL[A1, A2]: (A1 |*| (A2 |*| B)) -⚬ ((A1 |*| A2) |*| B) = timesAssocRL
    def outL[A1, A2]: ((A1 |*| A2) |*| B) -⚬ (A1 |*| (A2 |*| B)) = timesAssocLR
  }

  /** Product is covariant in the second argument. */
  implicit def snd[A]: Transportive[A |*| *] = new Transportive[A |*| *] {
    def lift[B1, B2](f: B1 -⚬ B2): (A |*| B1) -⚬ (A |*| B2) = liftSnd(f)
    def inL[B1, B2]: (B1 |*| (A |*| B2)) -⚬ (A |*| (B1 |*| B2)) =
      timesAssocRL[B1, A, B2].in.fst(swap).timesAssocLR
    def outL[B1, B2]: (A |*| (B1 |*| B2)) -⚬ (B1 |*| (A |*| B2)) =
      timesAssocRL[A, B1, B2].in.fst(swap).timesAssocLR
  }

  /** Disjoint union is covariant in the left argument. */
  def left[B]: Functor[* |+| B] = new Functor[* |+| B] {
    def lift[A1, A2](f: A1 -⚬ A2): (A1 |+| B) -⚬ (A2 |+| B) = liftL(f)
  }

  /** Disjoint union is covariant in the right argument. */
  def right[A]: Functor[A |+| *] = new Functor[A |+| *] {
    def lift[B1, B2](f: B1 -⚬ B2): (A |+| B1) -⚬ (A |+| B2) = liftR(f)
  }

  /** Choice is covariant in the left argument. */
  def choiceL[B]: Functor[* |&| B] = new Functor[* |&| B] {
    def lift[A1, A2](f: A1 -⚬ A2): (A1 |&| B) -⚬ (A2 |&| B) = choice[A1 |&| B, A2, B](chooseL andThen f, chooseR)
  }

  /** Choice is covariant in the right argument. */
  def choiceR[A]: Functor[A |&| *] = new Functor[A |&| *] {
    def lift[B1, B2](f: B1 -⚬ B2): (A |&| B1) -⚬ (A |&| B2) = choice[A |&| B1, A, B2](chooseL, chooseR andThen f)
  }

  /** Function object (exponential) is contravariant in the input type. */
  def input[C]: ContraFunctor[* =⚬ C] = new ContraFunctor[* =⚬ C] {
    def lift[A, B](f: A -⚬ B): (B =⚬ C) -⚬ (A =⚬ C) =
      id                       [(B =⚬ C) |*| A]
        .in.snd(f)          .to[(B =⚬ C) |*| B]
        .andThen(eval)      .to[C]
        .as[((B =⚬ C) |*| A) -⚬ C]
        .curry
  }

  /** Function object (exponential) is covariant in the output type. */
  def output[A]: Functor[A =⚬ *] = new Functor[A =⚬ *] {
    def lift[B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
      id                       [(A =⚬ B) |*| A]
        .andThen(eval)      .to[B]
        .andThen(f)         .to[C]
        .as[((A =⚬ B) |*| A) -⚬ C]
        .curry
  }

  implicit val tensorBifunctor: Bifunctor[|*|]= new Bifunctor[|*|] {
    def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |*| C) -⚬ (B |*| D) =
      par(f, g)
  }

  implicit val eitherBifunctor: Bifunctor[|+|] = new Bifunctor[|+|] {
    def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |+| C )-⚬ (B |+| D) =
      either(f andThen injectL, g andThen injectR)
  }

  implicit val choiceBifunctor: Bifunctor[|&|]= new Bifunctor[|&|] {
    def lift[A, B, C, D](f: A -⚬ B, g: C -⚬ D): (A |&| C) -⚬ (B |&| D) =
      choice(chooseL andThen f, chooseR andThen g)
  }

  implicit class LinearFunctionOps[A, B](self: A -⚬ B) {
    /** No-op used for documentation purposes: explicitly states the input type of this linear function. */
    def from[Z](implicit ev: A =:= Z): Z -⚬ B = ev.substituteCo[* -⚬ B](self)

    /** No-op used for documentation purposes: explicitly states the output type of this linear function. */
    def to[C](implicit ev: B =:= C): A -⚬ C = ev.substituteCo(self)

    /** No-op used for documentation purposes: explicitly states the full type of this linear function. */
    def as[C](implicit ev: (A -⚬ B) =:= C): C = ev(self)

    def andThen[C](g: B -⚬ C): A -⚬ C = dsl.andThen(self, g)

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

    def curry[A1, A2](implicit ev: A =:= (A1 |*| A2)): A1 -⚬ (A2 =⚬ B) =
      dsl.curry(ev.substituteCo[* -⚬ B](self))

    def uncurry[B1, B2](implicit ev: B =:= (B1 =⚬ B2)): (A |*| B1) -⚬ B2 =
      dsl.uncurry(ev.substituteCo(self))

    def timesAssocLR[B1, B2, B3](implicit ev: B =:= ((B1 |*| B2) |*| B3)): A -⚬ (B1 |*| (B2 |*| B3)) =
      ev.substituteCo(self) >>> dsl.timesAssocLR

    def timesAssocRL[B1, B2, B3](implicit ev: B =:= (B1 |*| (B2 |*| B3))): A -⚬ ((B1 |*| B2) |*| B3) =
      ev.substituteCo(self) >>> dsl.timesAssocRL

    def plusAssocLR[B1, B2, B3](implicit ev: B =:= ((B1 |+| B2) |+| B3)): A -⚬ (B1 |+| (B2 |+| B3)) =
      ev.substituteCo(self) >>> dsl.plusAssocLR

    def plusAssocRL[B1, B2, B3](implicit ev: B =:= (B1 |+| (B2 |+| B3))): A -⚬ ((B1 |+| B2) |+| B3) =
      ev.substituteCo(self) >>> dsl.plusAssocRL

    def distributeLR[B1, B2, B3](implicit ev: B =:= (B1 |*| (B2 |+| B3))): A -⚬ ((B1 |*| B2) |+| (B1 |*| B3)) =
      ev.substituteCo(self) >>> dsl.distributeLR

    def distributeRL[B1, B2, B3](implicit ev: B =:= ((B1 |+| B2) |*| B3)): A -⚬ ((B1 |*| B3) |+| (B2 |*| B3)) =
      ev.substituteCo(self) >>> dsl.distributeRL

    def pack[F[_]](implicit ev: B =:= F[Rec[F]]): A -⚬ Rec[F] =
      ev.substituteCo(self) >>> dsl.pack[F]

    def unpack[F[_]](implicit ev: B =:= Rec[F]): A -⚬ F[Rec[F]] =
      ev.substituteCo(self) >>> dsl.unpack[F]

    def race[B1: Completive, B2: Completive, C](
      caseFstWins: (B1 |*| B2) -⚬ C,
      caseSndWins: (B1 |*| B2) -⚬ C,
    )(implicit
      ev: B =:= (B1 |*| B2),
    ): A -⚬ C =
      ev.substituteCo(self) >>> dsl.race(caseFstWins, caseSndWins)

    def select[C1: Requisitive, C2: Requisitive](
      caseFstWins: B -⚬ (C1 |*| C2),
      caseSndWins: B -⚬ (C1 |*| C2),
    ): A -⚬ (C1 |*| C2) =
      self >>> dsl.select(caseFstWins, caseSndWins)

    def in: FocusedFunctionOutputCo[A, Id, B] = new FocusedFunctionOutputCo[A, Id, B](self)(idFunctor)
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
      f.zoomCo(lib.fst[B2])

    def snd: FocusedFunctionOutputCo[A, λ[x => F[B1 |*| x]], B2] =
      f.zoomCo(lib.snd[B1])
  }

  implicit class FocusedFunctionOutputOnPlusCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 |+| B2]) {
    def left: FocusedFunctionOutputCo[A, λ[x => F[x |+| B2]], B1] =
      f.zoomCo(lib.left[B2])

    def right: FocusedFunctionOutputCo[A, λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(lib.right[B1])
  }

  implicit class FocusedFunctionOutputOnChoiceCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 |&| B2]) {
    def choiceL: FocusedFunctionOutputCo[A, λ[x => F[x |&| B2]], B1] =
      f.zoomCo(lib.choiceL[B2])

    def choiceR: FocusedFunctionOutputCo[A, λ[x => F[B1 |&| x]], B2] =
      f.zoomCo(lib.choiceR[B1])
  }

  implicit class FocusedFunctionOutputOnFunctionCo[A, F[_], B1, B2](f: FocusedFunctionOutputCo[A, F, B1 =⚬ B2]) {
    def input: FocusedFunctionOutputContra[A, λ[x => F[x =⚬ B2]], B1] =
      f.zoomContra(lib.input[B2])

    def output: FocusedFunctionOutputCo[A, λ[x => F[B1 =⚬ x]], B2] =
      f.zoomCo(lib.output[B1])
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
      f.zoomCo(lib.fst[B2])

    def snd: FocusedFunctionOutputContra[A, λ[x => F[B1 |*| x]], B2] =
      f.zoomCo(lib.snd[B1])
  }

  implicit class FocusedFunctionOutputOnPlusContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 |+| B2]) {
    def left: FocusedFunctionOutputContra[A, λ[x => F[x |+| B2]], B1] =
      f.zoomCo(lib.left[B2])

    def right: FocusedFunctionOutputContra[A, λ[x => F[B1 |+| x]], B2] =
      f.zoomCo(lib.right[B1])
  }

  implicit class FocusedFunctionOutputOnChoiceContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 |&| B2]) {
    def choiceL: FocusedFunctionOutputContra[A, λ[x => F[x |&| B2]], B1] =
      f.zoomCo(lib.choiceL[B2])

    def choiceR: FocusedFunctionOutputContra[A, λ[x => F[B1 |&| x]], B2] =
      f.zoomCo(lib.choiceR[B1])
  }

  implicit class FocusedFunctionOutputOnFunctionContra[A, F[_], B1, B2](f: FocusedFunctionOutputContra[A, F, B1 =⚬ B2]) {
    def input: FocusedFunctionOutputCo[A, λ[x => F[x =⚬ B2]], B1] =
      f.zoomContra(lib.input[B2])

    def output: FocusedFunctionOutputContra[A, λ[x => F[B1 =⚬ x]], B2] =
      f.zoomCo(lib.output[B1])
  }

  def IXI[A, B, C, D]: ((A|*|B)|*|(C|*|D)) -⚬
  //                     |    \   /    |
  //                     |     \ /     |
  //                     |      X      |
  //                     |     / \     |
  //                     |    /   \    |
                       ((A|*|C)|*|(B|*|D)) =
    id                             [ (A |*| B) |*| (C |*| D) ]
      .timesAssocLR             .to[ A |*| (B |*| (C |*| D)) ]
      .in.snd(timesAssocRL)     .to[ A |*| ((B |*| C) |*| D) ]
      .in.snd.fst(swap)         .to[ A |*| ((C |*| B) |*| D) ]
      .in.snd(timesAssocLR)     .to[ A |*| (C |*| (B |*| D)) ]
      .timesAssocRL             .to[ (A |*| C) |*| (B |*| D) ]

  def IX[A, B, C]: ((A|*|B)|*| C) -⚬
    //               |    \   /
    //               |     \ /
    //               |      X
    //               |     / \
    //               |    /   \
                   ((A|*|C)|*| B) =
    timesAssocLR[A, B, C] >>> par(id, swap) >>> timesAssocRL

  def XI[A, B, C]: (A |*|(B|*|C)) -⚬
    //               \   /    |
    //                \ /     |
    //                 X      |
    //                / \     |
    //               /   \    |
                   (B |*|(A|*|C)) =
    timesAssocRL[A, B, C] >>> par(swap, id) >>> timesAssocLR

  def fakeDemand[A]: One -⚬ Neg[A] =
    id                                           [        One        ]
      .andThen(valNegDuality[A].introduce)    .to[ Val[A] |*| Neg[A] ]
      .andThen(discardFst)                    .to[            Neg[A] ]

  def mergeDemands[A]: (Neg[A] |*| Neg[A]) -⚬ Neg[A] =
    id                                         [   Neg[A] |*| Neg[A]                                       ]
      .introSnd(valNegDuality[A].introduce) .to[  (Neg[A] |*| Neg[A]) |*| (     Val[A]         |*| Neg[A]) ]
      .timesAssocRL                         .to[ ((Neg[A] |*| Neg[A]) |*|       Val[A]       ) |*| Neg[A]  ]
      .in.fst.snd(dup)                      .to[ ((Neg[A] |*| Neg[A]) |*| (Val[A] |*| Val[A])) |*| Neg[A]  ]
      .in.fst(IXI)                          .to[ ((Neg[A] |*| Val[A]) |*| (Neg[A] |*| Val[A])) |*| Neg[A]  ]
      .in.fst(parToOne(zap, zap))           .to[                      One                      |*| Neg[A]  ]
      .elimFst                              .to[                                                   Neg[A]  ]

  /** From the choice ''available'' on the right (`C |&| D`), choose the one corresponding to the choice ''made''
    * on the left (`A |+| B`): if on the left there is `A`, choose `C`, if on the left thre is `B`, choose `D`.
    */
  def matchingChoiceLR[A, B, C, D]: ((A |+| B) |*| (C |&| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |+| B) |*| (C |&| D)]
      .distributeRL            .to[(A |*| (C |&| D)) |+| (B |*| (C |&| D))]
      .in.left.snd(chooseL)    .to[(A |*|  C       ) |+| (B |*| (C |&| D))]
      .in.right.snd(chooseR)   .to[(A |*|  C       ) |+| (B |*|        D )]

  /** From the choice ''available'' on the left (`A |&| B`), choose the one corresponding to the choice ''made''
    * on the right (`C |+| D`): if on the right there is `C`, choose `A`, if on the right there is `D`, choose `B`.
    */
  def matchingChoiceRL[A, B, C, D]: ((A |&| B) |*| (C |+| D)) -⚬ ((A |*| C) |+| (B |*| D)) =
    id[(A |&| B) |*| (C |+| D)]
      .distributeLR            .to[((A |&| B) |*| C) |+| ((A |&| B) |*| D)]
      .in.left.fst(chooseL)    .to[( A        |*| C) |+| ((A |&| B) |*| D)]
      .in.right.fst(chooseR)   .to[( A        |*| C) |+| (       B  |*| D)]

  type Bool = One |+| One
  object Bool {
    val constTrue: One -⚬ Bool =
      injectL

    val constFalse: One -⚬ Bool =
      injectR

    def ifThenElse[A, B]: (Bool |*| (A |&| B)) -⚬ (A |+| B) =
      id                              [        Bool |*| (A |&| B)   ]
        .andThen(matchingChoiceLR) .to[ (One |*| A) |+| (One |*| B) ]
        .in.left(elimFst)          .to[          A  |+| (One |*| B) ]
        .in.right(elimFst)         .to[          A  |+|          B  ]

    def ifThenElse[A, B, C](ifTrue: A -⚬ B, ifFalse: A -⚬ C): (Bool |*| A) -⚬ (B |+| C) =
      id                                   [         Bool |*| A          ]
        .distributeRL                   .to[ (One |*| A) |+| (One |*| A) ]
        .bimap(elimFst[A], elimFst[A])  .to[          A  |+|          A  ]
        .bimap(ifTrue, ifFalse)         .to[          B  |+|          C  ]

    private val eitherToBoolean: Either[Unit, Unit] => Boolean = {
      case Left(())  => true
      case Right(()) => false
    }

    private val booleanToEither: Boolean => Either[Unit, Unit] = {
      case true => Left(())
      case false => Right(())
    }

    def liftBoolean: Val[Boolean] -⚬ Bool = {
      id                                     [ Val[Boolean] ]
        .andThen(liftV(booleanToEither))  .to[ Val[Either[Unit, Unit]] ]
        .andThen(liftEither)              .to[ Val[Unit] |+| Val[Unit] ]
        .in.left(discard)                 .to[    One    |+| Val[Unit] ]
        .in.right(discard)                .to[    One    |+|    One    ]
    }

    def unliftBoolean: Bool -⚬ Val[Boolean] =
      id[Bool]                            .to[    One    |+|    One    ]
      .in.left(const(()))                 .to[ Val[Unit] |+|    One    ]
      .in.right(const(()))                .to[ Val[Unit] |+| Val[Unit] ]
      .andThen(unliftEither)              .to[ Val[Either[Unit, Unit]] ]
      .andThen(liftV(eitherToBoolean))    .to[      Val[Boolean]       ]
  }

  import Bool._

  def liftBipredicate[A, B](p: (A, B) => Boolean): (Val[A] |*| Val[B]) -⚬ Bool =
    id                                            [ Val[A] |*| Val[B] ]
      .andThen(unliftPair)                     .to[   Val[(A, B)]     ]
      .andThen(liftV(p.tupled))                .to[   Val[Boolean]    ]
      .andThen(liftBoolean)                    .to[       Bool        ]

  def lt[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.lt)

  def lteq[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.lteq)

  def gt[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.gt)

  def gteq[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.gteq)

  def equiv[A](implicit ord: Ordering[A]): (Val[A] |*| Val[A]) -⚬ Bool =
    liftBipredicate(ord.equiv)

  private def testKeys[A, B, K](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
    pred: (K, K) => Boolean,
  ): (A |*| B) -⚬ (Bool |*| (A |*| B)) =
    id[A |*| B]
      .par(aKey, bKey)
      .andThen(IXI)
      .in.fst(liftBipredicate(pred))

  def ltBy[A, B, K](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ (Bool |*| (A |*| B)) =
    testKeys(aKey, bKey, ord.lt)

  def lteqBy[A, B, K](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ (Bool |*| (A |*| B)) =
    testKeys(aKey, bKey, ord.lteq)

  def gtBy[A, B, K](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ (Bool |*| (A |*| B)) =
    testKeys(aKey, bKey, ord.gt)

  def gteqBy[A, B, K](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ (Bool |*| (A |*| B)) =
    testKeys(aKey, bKey, ord.gteq)

  def equivBy[A, B, K](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
  )(implicit
    ord: Ordering[K],
  ): (A |*| B) -⚬ (Bool |*| (A |*| B)) =
    testKeys(aKey, bKey, ord.equiv)

  def sortBy[A, B, K: Ordering](
    aKey: A -⚬ (Val[K] |*| A),
    bKey: B -⚬ (Val[K] |*| B),
  )
  : (A |*| B) -⚬ ((A |*| B) |+| (B |*| A)) =
    lteqBy(aKey, bKey) >>> ifThenElse(id, swap)

  sealed trait CompareModule {
    type Compared[A, B]

    def compareBy[F[_]: Transportive, G[_]: Transportive, K: Ordering]
    : F[Val[K]] |*| G[Val[K]] -⚬ Compared[F[Val[K]], G[Val[K]]]

    def compared[A, B, C](
      caseLt: (A |*| B) -⚬ C,
      caseEq: (A |*| B) -⚬ C,
      caseGt: (A |*| B) -⚬ C,
    )
    : Compared[A, B] -⚬ C

    implicit def bifunctorCompared: Bifunctor[Compared]
  }

  val Compare: CompareModule = new CompareModule {
    type Compared[A, B] = (A |*| B) |+| ((A |*| B) |+| (A |*| B))

    def compareBy[F[_], G[_], K](implicit
      F: Transportive[F],
      G: Transportive[G],
      K: Ordering[K],
    ): F[Val[K]] |*| G[Val[K]] -⚬ Compared[F[Val[K]], G[Val[K]]] = {
      def compareKeys(cmp: Val[K] |*| Val[K] -⚬ Bool): F[Val[K]] |*| G[Val[K]] -⚬ (Bool |*| (F[Val[K]] |*| G[Val[K]])) =
        id                                   [  F[     Val[K]      ]  |*|  G[     Val[K]      ]  ]
          .in.fst.co[F].map(dup)          .to[  F[Val[K] |*| Val[K]]  |*|  G[     Val[K]      ]  ]
          .in.snd.co[G].map(dup)          .to[  F[Val[K] |*| Val[K]]  |*|  G[Val[K] |*| Val[K]]  ]
          .in.fst(F.outL).in.snd(G.outL)  .to[ (Val[K] |*| F[Val[K]]) |*| (Val[K] |*| G[Val[K]]) ]
          .andThen(IXI)                   .to[ (Val[K] |*| Val[K]) |*| (F[Val[K]] |*| G[Val[K]]) ]
          .in.fst(cmp)                    .to[        Bool         |*| (F[Val[K]] |*| G[Val[K]]) ]

      type A = F[Val[K]]
      type B = G[Val[K]]

      id                                   [           A |*| B                       ]
        .andThen(compareKeys(lt))       .to[ Bool |*| (A |*| B)                      ]
        .andThen(ifThenElse(id, id))    .to[ (A |*| B) |+|           (A |*| B)       ]
        .in.right(compareKeys(equiv))   .to[ (A |*| B) |+| (Bool |*| (A |*| B))      ]
        .in.right(ifThenElse(id, id))   .to[ (A |*| B) |+| ((A |*| B) |+| (A |*| B)) ]
    }

    def compared[A, B, C](
      caseLt: A |*| B -⚬ C,
      caseEq: A |*| B -⚬ C,
      caseGt: A |*| B -⚬ C,
    ): Compared[A, B] -⚬ C =
      either(caseLt, either(caseEq, caseGt))

    override def bifunctorCompared: Bifunctor[Compared] =
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

  def zapPremises[A, Ā, B, C](implicit ev: Dual[A, Ā]): ((A =⚬ B) |*| (Ā =⚬ C)) -⚬ (B |*| C) = {
    id                              [  (A =⚬ B) |*| (Ā =⚬ C)                ]
      .introSnd(ev.introduce)    .to[ ((A =⚬ B) |*| (Ā =⚬ C)) |*| (A |*| Ā) ]
      .andThen(IXI)              .to[ ((A =⚬ B) |*| A) |*| ((Ā =⚬ C) |*| Ā) ]
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
          .andThen(parFromOne(id, id))            .to[    One    |*|    One    ]
          .par(a.introduce, b.introduce)          .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
          .andThen(IXI)                           .to[ (A |*| B) |*| (Ȧ |*| Ḃ) ]
      }

      def eliminate: ((A |*| B) |*| (Ȧ |*| Ḃ)) -⚬ One = {
        id[(A |*| B) |*| (Ȧ |*| Ḃ)]               .to[ (A |*| B) |*| (Ȧ |*| Ḃ) ]
          .andThen(IXI)                           .to[ (A |*| Ȧ) |*| (B |*| Ḃ) ]
          .par(a.eliminate, b.eliminate)          .to[    One    |*|    One    ]
          .andThen(parToOne(id, id))              .to[           One           ]
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
      .timesAssocLR               .to[  A |*| (B  |*| Ā) ]
      .in.snd(swap)               .to[  A |*| (Ā  |*| B) ]
      .timesAssocRL               .to[ (A |*|  Ā) |*| B  ]
      .elimFst(ev.eliminate)      .to[                B  ]
      .as[ ((A |*| B) |*| Ā) -⚬ B ]
      .curry

  /** Make the function on the left ''"absorb"'' the value on the right and return it as part of its output. */
  def absorbR[A, B, C]: ((A =⚬ B) |*| C) -⚬ (A =⚬ (B |*| C)) =
    id[((A =⚬ B) |*| C) |*| A]  .to[ ((A =⚬ B) |*| C) |*| A ]
      .timesAssocLR             .to[ (A =⚬ B) |*| (C |*| A) ]
      .in.snd(swap)             .to[ (A =⚬ B) |*| (A |*| C) ]
      .timesAssocRL             .to[ ((A =⚬ B) |*| A) |*| C ]
      .in.fst(eval)             .to[        B         |*| C ]
      .as[ (((A =⚬ B) |*| C) |*| A) -⚬ (B |*| C) ]
      .curry

  type Maybe[A] = One |+| A
  object Maybe {
    def empty[A]: One -⚬ Maybe[A] =
      injectL

    def just[A]: A -⚬ Maybe[A] =
      injectR

    def liftOption[A]: Val[Option[A]] -⚬ Maybe[Val[A]] =
      id[Val[Option[A]]]                .to[ Val[Option[      A]] ]
        .andThen(liftV(_.toRight(())))  .to[ Val[Either[Unit, A]] ]
        .andThen(liftEither)            .to[ Val[Unit] |+| Val[A] ]
        .in.left(dsl.discard)           .to[   One     |+| Val[A] ]

    def unliftOption[A]: Maybe[Val[A]] -⚬ Val[Option[A]] =
      id[Maybe[Val[A]]]             .to[    One    |+| Val[A] ]
      .in.left(const(()))           .to[ Val[Unit] |+| Val[A] ]
      .andThen(unliftEither)        .to[ Val[Either[Unit, A]] ]
      .andThen(liftV(_.toOption))   .to[ Val[Option[A]]       ]

    def getOrElse[A](f: One -⚬ A): Maybe[A] -⚬ A =
      either(f, id)

    def discard[A](f: A -⚬ One): Maybe[A] -⚬ One =
      either(id, f)

    def discard[A](implicit A: Comonoid[A]): Maybe[A] -⚬ One =
      discard(A.counit)
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

  implicit def comonoidVal[A]: Comonoid[Val[A]] =
    new Comonoid[Val[A]] {
      def counit : Val[A] -⚬ One                 = discard
      def split  : Val[A] -⚬ (Val[A] |*| Val[A]) = dup
    }

  implicit def monoidNeg[A]: Monoid[Neg[A]] =
    new Monoid[Neg[A]] {
      def unit    :                 One -⚬ Neg[A] = fakeDemand
      def combine : (Neg[A] |*| Neg[A]) -⚬ Neg[A] = mergeDemands
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

  def getFst[A, B](implicit A: Comonoid[A]): (A |*| B) -⚬ (A |*| (A |*| B)) =
    id                             [     A     |*| B  ]
      .in.fst(A.split)          .to[ (A |*| A) |*| B  ]
      .timesAssocLR             .to[  A |*| (A |*| B) ]

  def getSnd[A, B](implicit B: Comonoid[B]): (A |*| B) -⚬ (B |*| (A |*| B)) =
    id                             [  A |*|     B     ]
      .in.snd(B.split)          .to[  A |*| (B |*| B) ]
      .timesAssocRL             .to[ (A |*| B) |*| B  ]
      .swap                     .to[  B |*| (A |*| B) ]

  def discardFst[A, B](implicit A: Comonoid[A]): (A |*| B) -⚬ B =
    id                             [  A  |*| B ]
      .elimFst(A.counit)        .to[         B ]

  def discardSnd[A, B](implicit B: Comonoid[B]): (A |*| B) -⚬ A =
    id                             [ A |*|  B  ]
      .elimSnd(B.counit)        .to[ A         ]
}
