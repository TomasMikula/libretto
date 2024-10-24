package libretto.puro

import libretto.cats.{Functor, Monad}
import libretto.lambda.{EnumModule, Extractor, Focus, MonoidalCategory, Partitioning, ClosedSymmetricMonoidalCategory}
import libretto.lambda.util.{SourcePos, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import libretto.util.Equal
import scala.annotation.targetName
import libretto.lambda.SemigroupalCategory

/** Defines the "pure" part of Libretto concurrency DSL.
 *  By "pure" we mean absence of any Scala functions inside.
 *
 * @see [[libretto.scaletto.Scaletto]] extension of [[Puro]] with support for embedding Scala functions.
 */
trait Puro {
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

  /** `-[A]` is a "demand" for `A`.
    *
    * Inverts the flow of information: whatever travels through `A` in one direction,
    * travels through `-[A]` in the opposite direction.
    */
  type -[A]

  /** Function object (a.k.a. internal hom), internal to the DSL,
    * that is, a function that can be on the input or output of a linear function (`-⚬`).
    * It must itself be used linearly (i.e. exactly once).
    * While `A -⚬ B` is a _morphism_ in a category, `A =⚬ B` is an _object_ in the category.
    * Existence of all function objects (internal homs) makes `-⚬` a _closed monoidal category._
    * In fact, it follows from the existence of inversions: `A =⚬ B` can be defined as `-[A] |*| B`.
    */
  type =⚬[A, B] = -[A] |*| B

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
  type Void

  /** Choice between `A` and `B`.
    * The consumer chooses whether to get `A` or `B` (but can get only one of them).
    * The producer has to be ready to provide either of them.
    */
  type |&|[A, B]

  /** Delimiter of fields in n-ary typedefs. */
  type ||[A, B]

  /** Used to describe named fields: `"label" :: Type`. */
  type ::[Label, T]

  type OneOf[Cases]

  val OneOf: EnumModule[-⚬, |*|, OneOf, ||, ::]

  protected val SumPartitioning: libretto.lambda.CoproductPartitioning[-⚬, |*|, |+|]

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

  /** Used to define recursive types. */
  type Rec[F[_]]

  /** Represents a callable subroutine (subprogram) accessible from inside the program.
   *
   * It can be used (called) any number of times.
   * As such, it is a more convenient equivalent of `Unlimited[A =⚬ B]`,
   * with an extension method to invoke the subroutine.
   */
  type Sub[A, B]

  /** Unsigned (i.e. non-negative) integer up to 31 bits.
    * Behavior on overflow is undefined.
    */
  type UInt31

  val UInt31: UInt31s

  /** The type of auxiliary placeholder variables used in construction of [[λ]]-expressions. */
  type $[A]

  opaque type ??[A] = $[-[A]]

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

  def absurd[A]: Void -⚬ A

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

  /**
    * ```
    *   ┏━━━━━━━━━━━┓
    *   ┞────┐      ┃
    *   ╎  A │┄┄┐   ┃
    *   ┟────┘  ┆   ┃
    *   ┃       ┆   ┃
    *   ┞────┐  ┆   ┃
    *   ╎-[A]│←┄┘   ┃
    *   ┟────┘      ┃
    *   ┗━━━━━━━━━━━┛
    * ```
    */
  def backvert[A]: (A |*| -[A]) -⚬ One

  /**
    * ```
    *   ┏━━━━━━┓
    *   ┃      ┞────┐
    *   ┃   ┌┄┄╎-[A]│
    *   ┃   ┆  ┟────┘
    *   ┃   ┆  ┃
    *   ┃   ┆  ┞────┐
    *   ┃   └┄→╎  A │
    *   ┃      ┟────┘
    *   ┗━━━━━━┛
    * ```
    */
  def forevert[A]: One -⚬ (-[A] |*| A)

  /**
    * ```
    *   ┏━━━━━━━━━━━┓
    *   ┃           ┞────┐
    *   ┞────┐      ╎-[A]│
    *   ╎ ⎡A⎤│      ┟────┘
    *   ╎-⎢⊗⎥│      ┃
    *   ╎ ⎣B⎦│      ┞────┐
    *   ┟────┘      ╎-[B]│
    *   ┃           ┟────┘
    *   ┗━━━━━━━━━━━┛
    * ```
    */
  def distributeInversion[A, B]: -[A |*| B] -⚬ (-[A] |*| -[B])

  /**
    * ```
    *   ┏━━━━━━━━━━━┓
    *   ┞────┐      ┃
    *   ╎-[A]│      ┞────┐
    *   ┟────┘      ╎ ⎡A⎤│
    *   ┃           ╎-⎢⊗⎥│
    *   ┞────┐      ╎ ⎣B⎦│
    *   ╎-[B]│      ┟────┘
    *   ┟────┘      ┃
    *   ┗━━━━━━━━━━━┛
    * ```
    */
  def factorOutInversion[A, B]: (-[A] |*| -[B]) -⚬ -[A |*| B]

  def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C) =
    introFst(forevert[B]) > assocLR > snd(swap > f)

  def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B =
    swap > assocRL > elimFst(backvert)

  def uncurry[A, B, C](f: A -⚬ (B =⚬ C)): (A |*| B) -⚬ C =
    andThen(par(f, id[B]), eval[B, C])

  /** Turn a function into a function object. */
  def obj[A, B](f: A -⚬ B): One -⚬ (A =⚬ B) =
    curry(andThen(elimFst, f))

  /** Map the output of a function object. */
  def out[A, B, C](f: B -⚬ C): (A =⚬ B) -⚬ (A =⚬ C) =
    snd(f)

  def invertOne: One -⚬ -[One] =
    forevert[One] > elimSnd

  def unInvertOne: -[One] -⚬ One =
    introFst > backvert[One]

  /** Double-inversion elimination. */
  def die[A]: -[-[A]] -⚬ A =
    introSnd(forevert[A]) > assocRL > elimFst(swap > backvert[-[A]])

  /** Double-inversion introduction. */
  def dii[A]: A -⚬ -[-[A]] =
    introFst(forevert[-[A]]) > assocLR > elimSnd(swap > backvert[A])

  def contrapositive[A, B](f: A -⚬ B): -[B] -⚬ -[A] =
    introFst(forevert[A] > snd(f)) > assocLR > elimSnd(backvert[B])

  def unContrapositive[A, B](f: -[A] -⚬ -[B]): B -⚬ A =
    dii[B] > contrapositive(f) > die[A]

  def distributeInversionInto_|+|[A, B]: -[A |+| B] -⚬ (-[A] |&| -[B]) =
    choice(
      contrapositive(injectL[A, B]),
      contrapositive(injectR[A, B]),
    )

  def factorInversionOutOf_|+|[A, B]: (-[A] |+| -[B]) -⚬ -[A |&| B] =
    either(
      contrapositive(chooseL[A, B]),
      contrapositive(chooseR[A, B]),
    )

  def distributeInversionInto_|&|[A, B]: -[A |&| B] -⚬ (-[A] |+| -[B]) =
    unContrapositive(distributeInversionInto_|+| > choice(chooseL > die, chooseR > die) > dii)

  def factorInversionOutOf_|&|[A, B]: (-[A] |&| -[B]) -⚬ -[A |+| B] =
    unContrapositive(die > either(dii > injectL, dii > injectR) > factorInversionOutOf_|+|)

  def invertClosure[A, B]: -[A =⚬ B] -⚬ (B =⚬ A) =
    distributeInversion > swap > snd(die)

  def unInvertClosure[A, B]: (A =⚬ B) -⚬ -[B =⚬ A] =
    snd(dii) > swap > factorOutInversion

  /** Uses the resource from the first in-port to satisfy the demand from the second in-port.
    * Alias for [[backvert]].
    */
  def supply[A]: (A |*| -[A]) -⚬ One =
    backvert[A]

  /** Creates a demand on the first out-port, channeling the provided resource to the second out-port.
    * Alias for [[forevert]].
    */
  def demand[A]: One -⚬ (-[A] |*| A) =
    forevert[A]

  /** Alias for [[die]]. */
  def doubleDemandElimination[A]: -[-[A]] -⚬ A =
    die[A]

  /** Alias for [[dii]]. */
  def doubleDemandIntroduction[A]: A -⚬ -[-[A]] =
    dii[A]

  /** Alias for [[distributeInversion]] */
  def demandSeparately[A, B]: -[A |*| B] -⚬ (-[A] |*| -[B]) =
    distributeInversion[A, B]

  /** Alias for [[factorOutInversion]]. */
  def demandTogether[A, B]: (-[A] |*| -[B]) -⚬ -[A |*| B] =
    factorOutInversion[A, B]

  /** Converts a demand for choice to a demand of the chosen side.
    * Alias for [[distributeInversionInto_|&|]].
    */
  def demandChosen[A, B]: -[A |&| B] -⚬ (-[A] |+| -[B]) =
    distributeInversionInto_|&|[A, B]

  /** Converts an obligation to handle either demand to an obligation to supply a choice.
    * Alias for [[factorInversionOutOf_|+|]].
    */
  def demandChoice[A, B]: (-[A] |+| -[B]) -⚬ -[A |&| B] =
    factorInversionOutOf_|+|[A, B]

  /** Converts demand for either to a choice of which side to supply.
    * Alias for [[distributeInversionInto_|+|]].
    */
  def toChoiceOfDemands[A, B]: -[A |+| B] -⚬ (-[A] |&| -[B]) =
    distributeInversionInto_|+|[A, B]

  /** Converts choice of demands to demand of either.
    * Alias for [[factorInversionOutOf_|&|]].
    */
  def demandEither[A, B]: (-[A] |&| -[B]) -⚬ -[A |+| B] =
    factorInversionOutOf_|&|[A, B]

  def invertedPingAsPong: -[Ping] -⚬ Pong =
    introFst(lInvertPongPing) > assocLR > elimSnd(supply[Ping])

  def pongAsInvertedPing: Pong -⚬ -[Ping] =
    introFst(demand[Ping]) > assocLR > elimSnd(rInvertPingPong)

  def invertedPongAsPing: -[Pong] -⚬ Ping =
    introSnd(lInvertPongPing) > assocRL > elimFst(swap > supply[Pong])

  def pingAsInvertedPong: Ping -⚬ -[Pong] =
    introSnd(demand[Pong] > swap) > assocRL > elimFst(rInvertPingPong)

  def invertedDoneAsNeed: -[Done] -⚬ Need =
    introFst(lInvertSignal) > assocLR > elimSnd(supply[Done])

  def needAsInvertedDone: Need -⚬ -[Done] =
    introFst(demand[Done]) > assocLR > elimSnd(rInvertSignal)

  def invertedNeedAsDone: -[Need] -⚬ Done =
    introSnd(lInvertSignal) > assocRL > elimFst(swap > supply[Need])

  def doneAsInvertedNeed: Done -⚬ -[Need] =
    introSnd(demand[Need] > swap) > assocRL > elimFst(rInvertSignal)

  def packDemand[F[_]]: -[F[Rec[F]]] -⚬ -[Rec[F]] =
    contrapositive(unpack[F])

  def unpackDemand[F[_]]: -[Rec[F]] -⚬ -[F[Rec[F]]] =
    contrapositive(pack[F])

  def fun[A, B]: Sub[A, B] -⚬ (A =⚬ B) =
    curry(invoke)

  def rec[A, B](using pos: SourcePos)(f: (A -⚬ B) => (A -⚬ B)): A -⚬ B

  def rec[A, B](f: (Sub[A, B] |*| A) -⚬ B): A -⚬ B

  /** An invocation of a subroutine. */
  def invoke[A, B]: (Sub[A, B] |*| A) -⚬ B

  /** A subroutine is available any number of times. */
  given comonoidSub[A, B]: Comonoid[Sub[A, B]]

  def sub[A, B](using pos: SourcePos)(f: A -⚬ B): One -⚬ Sub[A, B]

  def subroutine[A, B](f: A -⚬ B)(using SourcePos, LambdaContext): $[Sub[A, B]] =
    constant(sub(f))

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

  // TODO: make it `named(Id)(A -⚬ B)`, using a unique identifier
  def sharedCode[A, B](using SourcePos)(f: A -⚬ B): A -⚬ B

  given category: ClosedSymmetricMonoidalCategory[-⚬, |*|, One, =⚬]

  type LambdaContext

  val λ: LambdaOps

  trait LambdaOps {
    val closure: ClosureOps

    /** Used to define a linear function `A -⚬ B` in a point-full style, i.e. as a lambda expression.
      *
      * Recall that when defining `A -⚬ B`, we never get a hold of `a: A` as a Scala value. However,
      * by using this method we get a hold of `a: $[A]`, a placeholder variable, and construct the result
      * expression `$[B]`.
      * This method then inspects how the input variable `a: $[A]` is used in the result `$[B]` and
      * infers a (point-free) construction of `A -⚬ B`.
      *
      * @throws AssemblyError if `f` is malformed
      */
    def apply[A, B](using SourcePos)(
      f: LambdaContext ?=> $[A] => $[B],
    ): A -⚬ B

    def rec[A, B](using SourcePos)(
      f: LambdaContext ?=> $[Sub[A, B]] => $[A] => $[B],
    ): A -⚬ B =
      val g: (Sub[A, B] |*| A) -⚬ B = apply { case *(self) |*| a => f(self)(a) }
      Puro.this.rec(g)

    /** Auxiliary method to specify the type of input port. */
    def from[A]: LambdaFrom[A] =
      LambdaFrom[A]

    class LambdaFrom[A] {
      def apply[B](using SourcePos)(
        f: LambdaContext ?=> $[A] => $[B],
      ): A -⚬ B =
        LambdaOps.this.apply[A, B](f)

      def rec[B](using SourcePos)(
        f: LambdaContext ?=> $[Sub[A, B]] => $[A] => $[B],
      ): A -⚬ B =
        LambdaOps.this.rec[A, B](f)
    }
  }

  trait ClosureOps {
    /** Creates a closure (`A =⚬ B`), i.e. a function that captures variables from the outer scope,
      * as an expression (`$[A =⚬ B]`) that can be used in outer [[λ]].
      */
    def apply[A, B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[A] => $[B],
    ): $[A =⚬ B]

    def rec[A, B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[Sub[A, B]] => $[A] => $[B],
    ): $[A =⚬ B]

    /** Auxiliary method to specify the type of input port. */
    def from[A]: ClosureFrom[A] =
      ClosureFrom[A]

    class ClosureFrom[A] {
      def apply[B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[A] => $[B],
    ): $[A =⚬ B] =
        ClosureOps.this.apply[A, B](f)

      def rec[B](using SourcePos, LambdaContext)(
      f: LambdaContext ?=> $[Sub[A, B]] => $[A] => $[B],
    ): $[A =⚬ B] =
        ClosureOps.this.rec[A, B](f)
    }
  }

  object producing {
    def apply[B](using pos: SourcePos, ctx: LambdaContext)(
      f: LambdaContext ?=> ??[B] => ??[One]
    ): $[B] = {
      val g: $[-[-[B]] |*| -[One]] = λ.closure(f)
      val (b, negOne) = $.unzip(g)(pos)
      doubleDemandElimination(b) alsoElim ($.one supplyTo negOne)
    }

    def demand[B](using pos: SourcePos, ctx: LambdaContext)(
      f: LambdaContext ?=> $[B] => $[One]
    ): $[-[B]] = {
      val g: $[-[B] |*| One] = λ.closure(f)
      $.map(g)(elimSnd)(pos)
    }
  }

  type AssemblyError <: Throwable

  val $: $Ops

  trait $Ops {
    def one(using SourcePos, LambdaContext): $[One]

    def map[A, B](a: $[A])(f: A -⚬ B)(pos: SourcePos)(using
      LambdaContext,
    ): $[B]

    def zip[A, B](a: $[A], b: $[B])(pos: SourcePos)(using
      LambdaContext,
    ): $[A |*| B]

    def unzip[A, B](ab: $[A |*| B])(pos: SourcePos)(using
      LambdaContext,
    ): ($[A], $[B])

    def matchAgainst[A, B](a: $[A], extractor: Extractor[-⚬, |*|, A, B])(pos: SourcePos)(using
      LambdaContext
    ): $[B]

    def nonLinear[A](a: $[A])(
      split: Option[A -⚬ (A |*| A)],
      ditch: Option[A -⚬ One],
    )(
      pos: SourcePos,
    )(using
      LambdaContext,
    ): $[A]

    def eliminateFirst[A](unit: $[One], a: $[A])(
      pos: SourcePos,
    )(using LambdaContext): $[A] =
      map(zip(unit, a)(pos))(elimFst)(pos)

    def eliminateSecond[A](a: $[A], unit: $[One])(
      pos: SourcePos,
    )(using LambdaContext): $[A] =
      map(zip(a, unit)(pos))(elimSnd)(pos)

    def joinTwo(a: $[Done], b: $[Done])(
      pos: SourcePos,
    )(using LambdaContext): $[Done] =
      map(zip(a, b)(pos))(Puro.this.join)(pos)

    def app[A, B](f: $[A =⚬ B], a: $[A])(
      pos: SourcePos,
    )(using
      LambdaContext,
    ): $[B]
  }

  val |*| : ConcurrentPairOps

  trait ConcurrentPairOps {
    def unapply[A, B](ab: $[A |*| B])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ($[A], $[B]) =
      $.unzip(ab)(pos)

    @targetName("unapplyOutPair")
    def unapply[A, B](ab: ??[A |*| B])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): (??[A], ??[B]) =
      $.unzip($.map(ab)(distributeInversion)(pos))(pos)
  }

  object - {
    def unapply[A](a: $[-[A]])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): Some[??[A]] =
      Some(a)
  }

  object -- {
    def unapply[A](a: $[-[-[A]]])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): Some[$[A]] =
      Some(doubleDemandElimination(a))
  }

  def returning[A](a: $[A], as: $[One]*)(using
    pos: SourcePos,
    ctx: LambdaContext,
  ): $[A] = {
    def go(a: $[A], as: List[$[One]]): $[A] =
      as match
        case Nil => a
        case h :: t => go(a alsoElim h, t)
    go(a, as.toList)
  }

  @targetName("returningDemand")
  def returning[A](a: ??[A], as: ??[One]*)(using
    pos: SourcePos,
    ctx: LambdaContext,
  ): ??[A] = {
    def go(a: ??[A], as: List[??[One]]): ??[A] =
      as match
        case Nil => a
        case h :: t => go(a alsoElim h, t)
    go(a, as.toList)
  }

  extension [A, B](f: A -⚬ B) {
    @targetName("applyFun")
    def apply(a: $[A])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[B] =
      $.map(a)(f)(pos)

    def >[C](g: B -⚬ C): A -⚬ C =
      andThen(f, g)

    /** "Prepend" this function `A -⚬ B` to a demand `??[B]`, reducing it to a demand `??[A]`. */
    @targetName("contramapOutput")
    def >|(expr: ??[B])(using SourcePos, LambdaContext): ??[A] =
      expr contramap f

    /** Reduce the demand for `B` to a demand for `A` by the function `A -⚬ B`. */
    @deprecated("Renamed to >|")
    @targetName("contramapOut")
    def >>:(expr: ??[B])(using SourcePos, LambdaContext): ??[A] =
      expr contramap f
  }

  extension [A](a: $[A]) {
    def |*|[B](b: $[B])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[A |*| B] =
      $.zip(a, b)(pos)

    /** Alias for [[|>]] */
    @deprecated("Renamed to |>")
    def :>>[B](f: A -⚬ B)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[B] =
      a |> f

    /** Pipeline operator: pass this expression into the given function. */
    def |>[B](f: A -⚬ B)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[B] =
      $.map(a)(f)(pos)

    infix def alsoElim(unit: $[One])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[A] =
      $.eliminateFirst(unit, a)(pos)

    def also[B](f: One -⚬ B)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[A |*| B] =
      a |> introSnd(f)

    def alsoFst[X](f: One -⚬ X)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[X |*| A] =
      a |> introFst(f)

    infix def supplyTo(out: $[-[A]])(using pos: SourcePos, ctx: LambdaContext): $[One] =
      $.zip(a, out)(pos) |> supply

    @deprecated("Renamed to =:")
    def :>:(b: ??[A])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[One] =
      (a supplyTo b) |> invertOne

    def =:(b: ??[A])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[One] =
      (a supplyTo b) |> invertOne

    def alsoElimInv(x: $[-[One]])(using pos: SourcePos, ctx: LambdaContext): $[A] =
      a alsoElim (backvert($.one |*| x))

    def asOutput[B](rInvert: (A |*| B) -⚬ One)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[B] = {
      val (nb, b) = $.unzip(constant(demand[B]))(pos)
      returning(nb, rInvert(a |*| b))
    }
  }

  extension [A, B](f: $[A =⚬ B]) {
    def apply(a: $[A])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[B] =
      $.app(f, a)(pos)
  }

  extension [B](expr: $[-[B]]) {
    infix def contramap[A](f: A -⚬ B)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[-[A]] =
      $.map(expr)(contrapositive(f))(pos)

    infix def unInvertWith[A](lInvert: One -⚬ (A |*| B))(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[A] =
      $.unzip($.one |> lInvert)(pos) match {
        case (a, b) => a alsoElim (b supplyTo expr)
      }
  }

  extension [B](expr: ??[B]) {
    @targetName("zipOutPair")
    def |*|[C](that: ??[C])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[B |*| C] =
      $.zip(expr, that)(pos) |> demandTogether

    @targetName("set")
    def := (value: $[B])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[One] =
      value =: expr

    @targetName("alsoElimOut")
    infix def alsoElim(that: ??[One])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[B] =
      $.eliminateSecond(expr,  that |> unInvertOne)(pos)

    def asInput[A](lInvert: One -⚬ (B |*| A))(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[A] = {
      val ba = constant(lInvert)
      val (b, a) = $.unzip(ba)(pos)
      returning(a, b supplyTo expr)
    }

    def asInputInv(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[-[B]] =
      expr
  }

  extension [A, B](x: $[-[A |&| B]]) {
    @targetName("choose_-|&|")
    def choose[C](f: LambdaContext ?=> Either[$[-[A]], $[-[B]]] => $[C])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[C] =
      (x |> distributeInversionInto_|&|) either f
  }

  extension [A, B](x: ??[A |&| B]) {
    @targetName("choose_|&|")
    def choose[C](f: LambdaContext ?=> Either[??[A], ??[B]] => ??[C])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): ??[C] =
      (x |> distributeInversionInto_|&|) either f
  }

  extension [A](a: ??[-[A]]) {
    def asInput(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[A] =
      doubleDemandElimination(a)
  }

  extension [A, B](f: $[Sub[A, B]]) {
    @targetName("applySub")
    def apply(using pos: SourcePos, ctx: LambdaContext)(a: $[A]): $[B] =
      invoke(f |*| a)
  }

  extension (d: $[Done]) {
    infix def alsoJoin(others: $[Done]*)(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[Done] =
      joinAll(d, others*)(using pos)
  }

  def joinAll(a: $[Done], as: $[Done]*)(using pos: SourcePos, ctx: LambdaContext): $[Done] =
    as match {
      case Seq()  => a
      case Seq(b) => $.joinTwo(a, b)(pos)
      case as     => joinAll($.joinTwo(a, as.head)(pos), as.tail*)
    }

  protected def switch[A, R](using LambdaContext, SourcePos)(a: $[A])(
    cases: (SourcePos, LambdaContext ?=> $[A] => $[R])*
  ): $[R]

  def switch[A](using ctx: LambdaContext, pos: SourcePos)(a: $[A]): SwitchInit[A] =
    SwitchInit(ctx, pos, a)

  class SwitchInit[A](ctx: LambdaContext, switchPos: SourcePos, a: $[A]) {
    def is[R](using casePos: SourcePos)(f: LambdaContext ?=> $[A] => $[R]): Switch[A, R] =
      Switch(ctx, switchPos, a, (casePos, f) :: Nil)
  }

  class Switch[A, R](
    ctx: LambdaContext,
    pos: SourcePos,
    a: $[A],
    cases: List[(SourcePos, LambdaContext ?=> $[A] => $[R])],
  ) {
    def is(using casePos: SourcePos)(f: LambdaContext ?=> $[A] => $[R]): Switch[A, R] =
      Switch(ctx, pos, a, (casePos, f) :: cases)

    def end: $[R] =
      switch(using ctx, pos)(a)(cases.reverse*)
  }

  extension [A, B](ext: Extractor[-⚬, |*|, A, B]) {
    def unapply(using pos: SourcePos, ctx: LambdaContext)(a: $[A]): Some[$[B]] =
      Some($.matchAgainst(a, ext)(pos))

    def apply(using pos: SourcePos, ctx: LambdaContext)(b: $[B]): $[A] =
      $.map(b)(ext.reinject)(pos)

    def apply(): B -⚬ A =
      ext.reinject
  }

  def recPartitioning[F[_]](
    p: Partitioning[-⚬, |*|, F[Rec[F]]]
  ): Partitioning[-⚬, |*|, Rec[F]] { type Partition[P] = p.Partition[P] }

  extension [F[_], B](ext: Extractor[-⚬, |*|, F[Rec[F]], B]) {
    def afterUnpack: Extractor[-⚬, |*|, Rec[F], B] =
      Extractor(recPartitioning(ext.partitioning), ext.partition)
  }

  def InL[A, B]: Extractor[-⚬, |*|, A |+| B, A] =
    SumPartitioning.Inl[A, B]

  def InR[A, B]: Extractor[-⚬, |*|, A |+| B, B] =
    SumPartitioning.Inr[A, B]

  extension [A, B](x: $[A |+| B]) {
    @deprecated("""Use the more general pattern-matching:
      switch(expr)
        .is { case InL(a) => ... }
        .is { case InR(b) => ... }
        .end
    """)
    infix def either[C](f: LambdaContext ?=> Either[$[A], $[B]] => $[C])(using
      pos: SourcePos,
      ctx: LambdaContext,
    ): $[C] =
      Puro.this.switch(using ctx, pos)(x)(
        (pos, ctx ?=> { case InL(a) => f(Left(a)) }),
        (pos, ctx ?=> { case InR(b) => f(Right(b)) }),
      )
  }

  def constant[A](f: One -⚬ A)(using SourcePos, LambdaContext): $[A] =
    f($.one)

  trait UInt31s {
    /**
     *
     * @throws IllegalArgumentException if `n` is negative
     */
    def apply(n: Int): Done -⚬ UInt31

    def add: (UInt31 |*| UInt31) -⚬ UInt31
    def multiply: (UInt31 |*| UInt31) -⚬ UInt31
    def increment: UInt31 -⚬ UInt31
    def decrement: UInt31 -⚬ (Done |+| UInt31)

    def neglect: UInt31 -⚬ Done
  }

  object ? {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A])(using A: Affine[A]): Some[$[A]] =
      Some($.nonLinear(a)(split = None, ditch = Some(A.discard))(pos))
  }

  object + {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A])(using A: Cosemigroup[A]): Some[$[A]] =
      Some($.nonLinear(a)(Some(A.split), ditch = None)(pos))
  }

  object * {
    def unapply[A](using pos: SourcePos)(using LambdaContext)(a: $[A])(using A: Comonoid[A]): Some[$[A]] =
      Some($.nonLinear(a)(Some(A.split), Some(A.discard))(pos))
  }

  type Affine[A] = libretto.cats.Affine[-⚬, One, A]
  val Affine = libretto.cats.Affine

  trait Cosemigroup[A] extends libretto.cats.Cosemigroup[-⚬, |*|, A]:
    override def cat: SemigroupalCategory[-⚬, |*|] = category

  trait Comonoid[A] extends libretto.cats.Comonoid[-⚬, |*|, One, A] with Cosemigroup[A]:
    override def cat: MonoidalCategory[-⚬, |*|, One] = category

  given affineOne: Affine[One] =
    Affine.from(id[One])

  given affinePair[A, B](using A: Affine[A], B: Affine[B]): Affine[A |*| B] =
    Affine.from(andThen(par(A.discard, B.discard), elimFst))

  given affineEither[A, B](using A: Affine[A], B: Affine[B]): Affine[A |+| B] =
    Affine.from(either(A.discard, B.discard))

  given cosemigroupDone: Cosemigroup[Done] with {
    override def split: Done -⚬ (Done |*| Done) = fork
  }

  given cosemigroupPing: Cosemigroup[Ping] with {
    override def split: Ping -⚬ (Ping |*| Ping) = forkPing
  }

  given cosemigroupNeed: Cosemigroup[Need] with {
    override def split: Need -⚬ (Need |*| Need) = joinNeed
  }

  given cosemigroupPong: Cosemigroup[Pong] with {
    override def split: Pong -⚬ (Pong |*| Pong) = joinPong
  }

  given comonoidOne: Comonoid[One] with {
    override def counit: One -⚬ One = id[One]
    override def split: One -⚬ (One |*| One) = introSnd[One]
  }

  given comonoidPing: Comonoid[Ping] with {
    override def split  : Ping -⚬ (Ping |*| Ping) = forkPing
    override def counit : Ping -⚬ One             = dismissPing
  }

  given comonoidNeed: Comonoid[Need] with {
    override def split  : Need -⚬ (Need |*| Need) = joinNeed
    override def counit : Need -⚬ One             = need
  }

  given comonoidPong: Comonoid[Pong] with {
    override def split  : Pong -⚬ (Pong |*| Pong) = joinPong
    override def counit : Pong -⚬ One             = pong
  }

  extension [F[_], A](fa: $[F[A]])(using F: Functor[-⚬, F]) {
    def map[B](using SourcePos, LambdaContext)(f: A -⚬ B): $[F[B]] =
      fa |> F.lift(f)
  }
}