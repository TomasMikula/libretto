package libretto

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
  def λ[A, B](f: $[A] => $[B])(implicit
    file: sourcecode.File,
    line: sourcecode.Line,
  ): A -⚬ B

  type NotLinearException <: Throwable
  type UnboundVariablesException <: Throwable

  val $: $Ops

  trait $Ops {
    def map[A, B](a: $[A])(f: A -⚬ B)(
      file: String,
      line: Int,
    ): $[B]

    def zip[A, B](a: $[A], b: $[B])(
      file: String,
      line: Int,
    ): $[A |*| B]

    def unzip[A, B](ab: $[A |*| B])(
      file: String,
      line: Int,
    ): ($[A], $[B])

    object |*| {
      def unapply[A, B](ab: $[A |*| B])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): ($[A], $[B]) =
        unzip(ab)(file.value, line.value)
    }

    extension [A, B](f: A -⚬ B) {
      def apply(a: $[A])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[B] =
        map(a)(f)(file.value, line.value)
    }

    extension [A](a: $[A]) {
      def |*|[B](b: $[B])(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[A |*| B] =
        zip(a, b)(file.value, line.value)

      def >[B](f: A -⚬ B)(implicit
        file: sourcecode.File,
        line: sourcecode.Line,
      ): $[B] =
        map(a)(f)(file.value, line.value)

      def also[B](f: One -⚬ B): $[A |*| B] =
        a > introSnd(f)

      def alsoFst[X](f: One -⚬ X): $[X |*| A] =
        a > introFst(f)

      def alsoElim(unit: $[One]): $[A] =
        (unit |*| a) > elimFst
    }
  }
}