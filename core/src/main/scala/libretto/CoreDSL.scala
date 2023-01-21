package libretto

import libretto.util.{Equal, SourcePos}

trait CoreDSL {
  /** Libretto arrow, also called a ''component'' or a ''linear function''.
    *
    * ```
    * ┏━━━━━━━━━━┓
    * ┞───┐      ┞───┐
    * ╎ A │      ╎ B │
    * ┟───┘      ┟───┘
    * ┗━━━━━━━━━━┛
    * ```
    *
    * In `A -⚬ B`, we say that the ''in-port'' is of type `A` and the ''out-port'' is of type `B`.
    * Note that the distinction between the in-port and the out-port is only formal. Information or resources
    * may flow in and out through both the in-port and the out-port.
    *
    * "Linear" means that each input is ''consumed'' exactly once, in particular, it cannot be ignored or used twice.
    */
  type -⚬[A, B]

  /** Concurrent pair. Also called a ''tensor product'' or simply ''times''. */
  type |*|[A, B]

  /** Alias for [[|*|]]. */
  type ⊗[A, B] = A |*| B

  /** No resource. It is the identity element for [[|*|]].
    * There is no flow of information through a `One`-typed port.
    */
  type One

  /** Either `A` or `B`. Analogous to [[scala.Either]].
    * Whether it is going to be `A` or `B` is decided by the producer.
    * The consumer has to be ready to handle either of the two cases.
    */
  type |+|[A, B]

  /** Alias for [[|+|]]. */
  type ⊕[A, B] = A |+| B

  /** Impossible resource. Analogous to [[Nothing]]. It is the identity element for [[|+|]]. */
  type Zero

  /** Choice between `A` and `B`.
    * The consumer chooses whether to get `A` or `B` (but can get only one of them).
    * The producer has to be ready to provide either of them.
    */
  type |&|[A, B]

  /** Signal that travels in the direction of [[-⚬]], i.e. the positive direction.
    * It may signal completion of a (potentially effectful) computation.
    * It cannot be ignored. (If this signal was the only handle to an (effectful) computation,
    * ignoring it would mean losing track of that computation, which is considered to be a resource leak.)
    */
  type Done

  /** Signal that travels in the direction opposite to [[-⚬]], i.e. the negative direction.
    * It may signal completion of a (potentially effectful) computation.
    * It cannot be ignored. (If this signal was the only handle to an (effectful) computation,
    * ignoring it would mean losing track of that computation, which is considered to be a resource leak.)
    */
  type Need

  /** Signal that travels in the direction of [[-⚬]], i.e. the positive direction.
    * [Unlike [[Done]], it cannot be the only handle to an effectful computation.
    * As such, it can be ignored, e.g. as the losing contestant in [[racePair]].
    */
  type Ping

  /** Signal that travels in the direction opposite to [[-⚬]], i.e. the negative direction.
    * Unlike [[Need]], it cannot be the only handle to an effectful computation.
    * As such, it can be ignored, e.g. as the losing contestant in [[selectPair]].
    */
  type Pong

  /** A black hole that can absorb (i.e. take over the responsibility to await) [[Done]] signals, but from which there
    * is no escape.
    */
  type RTerminus

  /** A black hole that can absorb (i.e. take over the responsibility to await) [[Need]] signals, but from which there
    * is no escape.
    */
  type LTerminus

  type Rec[F[_]]

  /** The type of auxiliary placeholder variables used in construction of [[λ]]-expressions. */
  type $[A]

  def id[A]: A -⚬ A

  def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C

  def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D)

  def fst[A, B, C](f: A -⚬ B): (A |*| C) -⚬ (B |*| C) =
    par(f, id[C])

  def snd[A, B, C](f: B -⚬ C): (A |*| B) -⚬ (A |*| C) =
    par(id[A], f)

  def introFst[B]: B -⚬ (One |*| B)
  def introSnd[A]: A -⚬ (A |*| One)
  def elimFst[B]: (One |*| B) -⚬ B
  def elimSnd[A]: (A |*| One) -⚬ A

  def introFst[A, X](f: One -⚬ X): A -⚬ (X |*| A) =
    andThen(introFst[A], par(f, id))

  def introSnd[A, X](f: One -⚬ X): A -⚬ (A |*| X) =
    andThen(introSnd[A], par(id, f))

  def elimFst[A, B](f: A -⚬ One): (A |*| B) -⚬ B =
    andThen(par(f, id), elimFst)

  def elimSnd[A, B](f: B -⚬ One): (A |*| B) -⚬ A =
    andThen(par(id, f), elimSnd)

  def assocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C))
  def assocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C)

  def swap[A, B]: (A |*| B) -⚬ (B |*| A)

  def injectL[A, B]: A -⚬ (A |+| B)
  def injectR[A, B]: B -⚬ (A |+| B)

  def either[A, B, C](
    caseLeft:  A -⚬ C,
    caseRight: B -⚬ C,
  ): (A |+| B) -⚬ C

  def chooseL[A, B]: (A |&| B) -⚬ A
  def chooseR[A, B]: (A |&| B) -⚬ B

  def choice[A, B, C](
    caseLeft:  A -⚬ B,
    caseRight: A -⚬ C,
  ): A -⚬ (B |&| C)

  def delayIndefinitely: Done -⚬ RTerminus
  def regressInfinitely: LTerminus -⚬ Need

  def fork: Done -⚬ (Done |*| Done)
  def join: (Done |*| Done) -⚬ Done

  def forkMap[A, B](f: Done -⚬ A, g: Done -⚬ B): Done -⚬ (A |*| B) =
    andThen(fork, par(f, g))

  def joinMap[A, B](f: A -⚬ Done, g: B -⚬ Done): (A |*| B) -⚬ Done =
    andThen(par(f, g), join)

  def forkNeed: (Need |*| Need) -⚬ Need
  def joinNeed: Need -⚬ (Need |*| Need)

  def forkMapNeed[A, B](f: A -⚬ Need, g: B -⚬ Need): (A |*| B) -⚬ Need =
    andThen(par(f, g), forkNeed)

  def joinMapNeed[A, B](f: Need -⚬ A, g: Need -⚬ B): Need -⚬ (A |*| B) =
    andThen(joinNeed, par(f, g))

  def notifyDoneL: Done -⚬ (Ping |*| Done)
  def notifyDoneR: Done -⚬ (Done |*| Ping) =
    andThen(notifyDoneL, swap)

  def notifyNeedL: (Pong |*| Need) -⚬ Need
  def notifyNeedR: (Need |*| Pong) -⚬ Need =
    andThen(swap, notifyNeedL)

  def forkPing: Ping -⚬ (Ping |*| Ping)
  def forkPong: (Pong |*| Pong) -⚬ Pong
  def joinPing: (Ping |*| Ping) -⚬ Ping
  def joinPong: Pong -⚬ (Pong |*| Pong)

  def strengthenPing: Ping -⚬ Done
  def strengthenPong: Need -⚬ Pong

  def ping: One -⚬ Ping
  def pong: Pong -⚬ One

  def done: One -⚬ Done = andThen(ping, strengthenPing)
  def need: Need -⚬ One = andThen(strengthenPong, pong)

  /** Signals when it is decided whether `A |+| B` actually contains the left side or the right side. */
  def notifyEither[A, B]: (A |+| B) -⚬ (Ping |*| (A |+| B))

  /** Signals (in the negative direction) when it is known which side of the choice (`A |&| B`) has been chosen. */
  def notifyChoice[A, B]: (Pong |*| (A |&| B)) -⚬ (A |&| B)

  def injectLOnPing[A, B]: (Ping |*| A) -⚬ (A |+| B)
  def injectROnPing[A, B]: (Ping |*| B) -⚬ (A |+| B) =
    andThen(injectLOnPing, either(injectR, injectL))

  def chooseLOnPong[A, B]: (A |&| B) -⚬ (Pong |*| A)
  def chooseROnPong[A, B]: (A |&| B) -⚬ (Pong |*| B) =
    andThen(choice(chooseR, chooseL), chooseLOnPong)

  def dismissPing: Ping -⚬ One =
    andThen(andThen(introSnd, injectLOnPing[One, One]), either(id, id))

  def dismissPong: One -⚬ Pong =
    andThen(choice(id, id), andThen(chooseLOnPong[One, One], elimSnd))

  /** Factor out the factor `A` on the left of both summands. */
  def factorL[A, B, C]: ((A |*| B) |+| (A |*| C)) -⚬ (A |*| (B |+| C)) =
    either(par(id, injectL), par(id, injectR))

  /** Factor out the factor `C` on the right of both summands. */
  def factorR[A, B, C]: ((A |*| C) |+| (B |*| C)) -⚬ ((A |+| B) |*| C) =
    either(par(injectL, id), par(injectR, id))

  /** Distribute the factor on the left into the summands on the right.
    * Inverse of [[factorL]].
    */
  def distributeL[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C))

  /** Distribute the factor on the right into the summands on the left.
    * Inverse of [[factorR]].
    */
  def distributeR[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C)) =
    andThen(andThen(swap, distributeL), either(andThen(swap, injectL), andThen(swap, injectR)))

  def coFactorL[A, B, C]: (A |*| (B |&| C)) -⚬ ((A |*| B) |&| (A |*| C)) =
    choice(par(id, chooseL), par(id, chooseR))

  def coFactorR[A, B, C]: ((A |&| B) |*| C) -⚬ ((A |*| C) |&| (B |*| C)) =
    choice(par(chooseL, id), par(chooseR, id))

  /** Inverse of [[coFactorL]]. */
  def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C))

  /** Inverse of [[coFactorR]]. */
  def coDistributeR[A, B, C]: ((A |*| C) |&| (B |*| C)) -⚬ ((A |&| B) |*| C) =
    andThen(andThen(choice(andThen(chooseL, swap), andThen(chooseR, swap)), coDistributeL), swap)

  /** Reverses the [[Done]] signal (flowing in the positive direction, i.e. along the `-⚬` arrow)
    * into a [[Need]] signal (flowing in the negative direciton, i.e. against the `-⚬` arrow).
    *
    * ```
    *   ┏━━━━━━━━━━━┓
    *   ┞────┐      ┃
    *   ╎Done│┄┄┐   ┃
    *   ┟────┘  ┆   ┃
    *   ┃       ┆   ┃
    *   ┞────┐  ┆   ┃
    *   ╎Need│←┄┘   ┃
    *   ┟────┘      ┃
    *   ┗━━━━━━━━━━━┛
    * ```
    */
  def rInvertSignal: (Done |*| Need) -⚬ One

  /** Reverses the [[Need]] signal (flowing in the negative direciton, i.e. against the `-⚬` arrow)
    * into a [[Done]] signal (flowing in the positive direction, i.e. along the `-⚬` arrow).
    *
    * ```
    *   ┏━━━━━━┓
    *   ┃      ┞────┐
    *   ┃   ┌┄┄╎Need│
    *   ┃   ┆  ┟────┘
    *   ┃   ┆  ┃
    *   ┃   ┆  ┞────┐
    *   ┃   └┄→╎Done│
    *   ┃      ┟────┘
    *   ┗━━━━━━┛
    * ```
    */
  def lInvertSignal: One -⚬ (Need |*| Done)

  def rInvertPingPong: (Ping |*| Pong) -⚬ One
  def lInvertPongPing: One -⚬ (Pong |*| Ping)

  def joinRTermini: (RTerminus |*| RTerminus) -⚬ RTerminus
  def joinLTermini: LTerminus -⚬ (LTerminus |*| LTerminus)

  def rInvertTerminus: (RTerminus |*| LTerminus) -⚬ One
  def lInvertTerminus: One -⚬ (LTerminus |*| RTerminus)

  def rec[A, B](f: (A -⚬ B) => (A -⚬ B)): A -⚬ B

  /** Hides one level of a recursive type definition. */
  def pack[F[_]]: F[Rec[F]] -⚬ Rec[F]

  /** Unpacks one level of a recursive type definition. */
  def unpack[F[_]]: Rec[F] -⚬ F[Rec[F]]

  /** Races the two [[Ping]] signals.
    * Produces left if the first signal wins and right if the second signal wins.
    * It is biased to the left: if both signals have arrived by the time of inquiry, returns left.
    */
  def racePair: (Ping |*| Ping) -⚬ (One |+| One)

  /** Races the two [[Pong]] signals (traveling from right to left).
    * Chooses left if the first signal wins and right if the second signal wins.
    * It is biased to the left: if both signals have arrived by the time of inquiry, chooses left.
    */
  def selectPair: (One |&| One) -⚬ (Pong |*| Pong)

  val λ: LambdaOps

  trait LambdaOps {
    type Ctx

    /** Used to define a linear function `A -⚬ B` in a point-full style, i.e. as a lambda expression.
      *
      * Recall that when defining `A -⚬ B`, we never get a hold of `a: A` as a Scala value. However,
      * by using this method we get a hold of `a: $[A]`, a placeholder variable, and construct the result
      * expression `$[B]`.
      * This method then inspects how the input variable `a: $[A]` is used in the result `$[B]` and
      * infers a (point-free) construction of `A -⚬ B`.
      *
      * @throws NotLinearException if the given function violates linearity, i.e. if the input variable
      *   is not used exactly once.
      * @throws UnboundVariablesException if the result expression contains free variables (from outer [[λ]]s).
      */
    def apply[A, B](using SourcePos)(
      f: Ctx ?=> $[A] => $[B],
    ): A -⚬ B

    def ?[A, B](using SourcePos)(
      f: Ctx ?=> $[A] => $[B],
    )(using
      Affine[A],
    ): A -⚬ B =
      apply { case $.?(a) => f(a) }

    def +[A, B](using SourcePos)(
      f: Ctx ?=> $[A] => $[B],
    )(using
      Cosemigroup[A],
    ): A -⚬ B =
      apply { case $.+(a) => f(a) }

    def *[A, B](using SourcePos)(
      f: Ctx ?=> $[A] => $[B],
    )(using
      Comonoid[A],
    ): A -⚬ B =
      apply { case $.*(a) => f(a) }
  }

  type NotLinearException <: Throwable
  type UnboundVariablesException <: Throwable

  val $: $Ops

  trait $Ops {
    def one(implicit pos: SourcePos): $[One]

    def map[A, B](a: $[A])(f: A -⚬ B)(
      pos: SourcePos,
    ): $[B]

    def zip[A, B](a: $[A], b: $[B])(
      pos: SourcePos,
    ): $[A |*| B]

    def unzip[A, B](ab: $[A |*| B])(
      pos: SourcePos,
    ): ($[A], $[B])

    def nonLinear[A](a: $[A])(
      split: Option[A -⚬ (A |*| A)],
      ditch: Option[A -⚬ One],
    )(
      pos: SourcePos,
    ): $[A]

    def eliminateFirst[A](unit: $[One], a: $[A])(
      pos: SourcePos,
    ): $[A] =
      map(zip(unit, a)(pos))(elimFst)(pos)

    def eliminateSecond[A](a: $[A], unit: $[One])(
      pos: SourcePos,
    ): $[A] =
      map(zip(a, unit)(pos))(elimSnd)(pos)

    def joinTwo(a: $[Done], b: $[Done])(
      pos: SourcePos,
    ): $[Done] =
      map(zip(a, b)(pos))(CoreDSL.this.join)(pos)

    def joinAll(a: $[Done], as: $[Done]*)(using pos: SourcePos): $[Done] =
      as match {
        case Seq()  => a
        case Seq(b) => joinTwo(a, b)(pos)
        case as     => joinAll(joinTwo(a, as.head)(pos), as.tail: _*)
      }

    object |*| {
      def unapply[A, B](ab: $[A |*| B])(using
        pos: SourcePos,
      ): ($[A], $[B]) =
        unzip(ab)(pos)
    }

    object ? {
      def unapply[A](using pos: SourcePos)(a: $[A])(using A: Affine[A]): Some[$[A]] =
        Some(nonLinear(a)(split = None, ditch = Some(A.discard))(pos))
    }

    object + {
      def unapply[A](using pos: SourcePos)(a: $[A])(using A: Cosemigroup[A]): Some[$[A]] =
        Some(nonLinear(a)(Some(A.split), ditch = None)(pos))
    }

    object * {
      def unapply[A](using pos: SourcePos)(a: $[A])(using A: Comonoid[A]): Some[$[A]] =
        Some(nonLinear(a)(Some(A.split), Some(A.discard))(pos))
    }

    extension [A, B](f: A -⚬ B) {
      def apply(a: $[A])(using
        pos: SourcePos,
      ): $[B] =
        map(a)(f)(pos)
    }

    extension [A](a: $[A]) {
      def |*|[B](b: $[B])(using
        pos: SourcePos,
      ): $[A |*| B] =
        zip(a, b)(pos)

      def >[B](f: A -⚬ B)(using
        pos: SourcePos,
      ): $[B] =
        map(a)(f)(pos)

      // TODO: source position
      def also[B](f: One -⚬ B): $[A |*| B] =
        a > introSnd(f)

      // TODO: source position
      def alsoFst[X](f: One -⚬ X): $[X |*| A] =
        a > introFst(f)

      def alsoElim(unit: $[One])(using
        pos: SourcePos,
      ): $[A] =
        eliminateFirst(unit, a)(pos)
    }

    extension (d: $[Done]) {
      def alsoJoin(others: $[Done]*)(using
        pos: SourcePos,
      ): $[Done] =
        joinAll(d, others: _*)(using pos)
    }

    implicit class FunctorOps[F[_], A](fa: $[F[A]]) {
      def map[B](f: $[A] => $[B])(using F: Functor[-⚬, F]): $[F[B]] =
        fa > F.lift(λ(f))

      def flatMap[B](f: $[A] => $[F[B]])(using F: Monad[-⚬, F]): $[F[B]] =
        fa > F.liftF(λ(f))
    }
  }

  trait Affine[A] {
    def discard: A -⚬ One
  }

  object Affine {
    def apply[A](using ev: Affine[A]): Affine[A] =
      ev

    def from[A](f: A -⚬ One): Affine[A] =
      new Affine[A] {
        override def discard: A -⚬ One =
          f
      }

    given affineOne: Affine[One] =
      from(id[One])

    given affinePair[A, B](using A: Affine[A], B: Affine[B]): Affine[A |*| B] =
      from(andThen(par(A.discard, B.discard), elimFst))
  }

  trait Cosemigroup[A] {
    def split: A -⚬ (A |*| A)

    def law_coAssociativity: Equal[ A -⚬ ((A |*| A) |*| A) ] =
      Equal(
        andThen(split, par(split, id[A])),
        andThen(andThen(split, par(id[A], split)), assocRL),
      )
  }

  object Cosemigroup {
    def apply[A](using ev: Cosemigroup[A]): Cosemigroup[A] =
      ev

    implicit val cosemigroupDone: Cosemigroup[Done] =
      new Cosemigroup[Done] {
        override def split: Done -⚬ (Done |*| Done) = fork
      }

    implicit val cosemigroupPing: Cosemigroup[Ping] =
      new Cosemigroup[Ping] {
        override def split: Ping -⚬ (Ping |*| Ping) = forkPing
      }

    implicit val cosemigroupNeed: Cosemigroup[Need] =
      new Cosemigroup[Need] {
        override def split: Need -⚬ (Need |*| Need) = joinNeed
      }

    implicit val cosemigroupPong: Cosemigroup[Pong] =
      new Cosemigroup[Pong] {
        override def split: Pong -⚬ (Pong |*| Pong) = joinPong
      }
  }

  trait Comonoid[A] extends Cosemigroup[A] with Affine[A] {
    def counit: A -⚬ One

    override def discard: A -⚬ One =
      counit

    def law_leftCounit: Equal[ A -⚬ (One |*| A) ] =
      Equal(
        andThen(this.split, par(counit, id[A])),
        introFst,
      )

    def law_rightCounit: Equal[ A -⚬ (A |*| One) ] =
      Equal(
        andThen(this.split, par(id[A], counit)),
        introSnd,
      )
  }

  object Comonoid {
    def apply[A](using ev: Comonoid[A]): Comonoid[A] =
      ev

    implicit val comonoidOne: Comonoid[One] =
      new Comonoid[One] {
        override def counit: One -⚬ One = id[One]
        override def split: One -⚬ (One |*| One) = introSnd[One]
      }

    implicit val comonoidPing: Comonoid[Ping] =
      new Comonoid[Ping] {
        override def split  : Ping -⚬ (Ping |*| Ping) = forkPing
        override def counit : Ping -⚬ One             = dismissPing
      }

    implicit val comonoidNeed: Comonoid[Need] =
      new Comonoid[Need] {
        override def split  : Need -⚬ (Need |*| Need) = joinNeed
        override def counit : Need -⚬ One             = need
      }

    implicit val comonoidPong: Comonoid[Pong] =
      new Comonoid[Pong] {
        override def split  : Pong -⚬ (Pong |*| Pong) = joinPong
        override def counit : Pong -⚬ One             = pong
      }
  }
}