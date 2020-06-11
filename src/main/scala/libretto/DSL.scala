package libretto

trait DSL {
  /** `A -⚬ B` is a function that ''consumes'' a resource of type `A` and produces a resource of type `B`.
    * Also known as linear implication.
    */
  type -⚬[A, B]

  /** Both `A` and `B`, concurrently. */
  type |*|[A, B]

  /** No resource. Analogous to [[Unit]]. It is the identity element for [[|*|]]. */
  type One

  /** Either `A` or `B`. Analogous to [[Either]].
    * The producer decides which one it is, the consumer can check which one it is.
    */
  type |+|[A, B]

  /** Impossible resource. Analogous to [[Nothing]]. It is the identity element for [[|+|]]. */
  type Zero

  /** Choose `A` or `B`. The consumer chooses whether to get `A` or `B`, but can get only one of them. */
  type |&|[A, B]

  /** Linear function as data, that is, one that can be part of an input or output of a linear function (`-⚬`).
    * While `A -⚬ B` is a morphism in a category, `A =⚬ B` is an exponential object.
    */
  type =⚬[A, B]

  /** Available value of type `A`. */
  type Val[A]

  /** Demand for a value of type `A`. */
  type Neg[A]

  type Rec[F[_]]

  /** An element of type `A` is represented as a function `One -⚬ A`. */
  type Elem[A] = One -⚬ A

  def id[A]: A -⚬ A

  def andThen[A, B, C](f: A -⚬ B, g: B -⚬ C): A -⚬ C

  def par[A, B, C, D](
    f: A -⚬ B,
    g: C -⚬ D,
  ): (A |*| C) -⚬ (B |*| D)

  def introFst[B]: B -⚬ (One |*| B)
  def introSnd[A]: A -⚬ (A |*| One)
  def elimFst[B]: (One |*| B) -⚬ B
  def elimSnd[A]: (A |*| One) -⚬ A

  def timesAssocLR[A, B, C]: ((A |*| B) |*| C) -⚬ (A |*| (B |*| C))
  def timesAssocRL[A, B, C]: (A |*| (B |*| C)) -⚬ ((A |*| B) |*| C)

  def injectL[A, B]: A -⚬ (A |+| B)
  def injectR[A, B]: B -⚬ (A |+| B)

  def either[A, B, C](f: A -⚬ C, g: B -⚬ C): (A |+| B) -⚬ C

  def plusAssocLR[A, B, C]: ((A |+| B) |+| C) -⚬ (A |+| (B |+| C))
  def plusAssocRL[A, B, C]: (A |+| (B |+| C)) -⚬ ((A |+| B) |+| C)

  def swap[A, B]: (A |*| B) -⚬ (B |*| A)

  def chooseL[A, B]: (A |&| B) -⚬ A
  def chooseR[A, B]: (A |&| B) -⚬ B

  def choice[A, B, C](f: A -⚬ B, g: A -⚬ C): A -⚬ (B |&| C)

  def distributeR[A, B, C]: (A |*| (B |+| C)) -⚬ ((A |*| B) |+| (A |*| C))
  def distributeL[A, B, C]: ((A |+| B) |*| C) -⚬ ((A |*| C) |+| (B |*| C))

  def coDistributeL[A, B, C]: ((A |*| B) |&| (A |*| C)) -⚬ (A |*| (B |&| C))
  def coDistributeR[A, B, C]: ((A |*| C) |&| (B |*| C)) -⚬ ((A |&| B) |*| C)

  def curry[A, B, C](f: (A |*| B) -⚬ C): A -⚬ (B =⚬ C)
  def eval[A, B]: ((A =⚬ B) |*| A) -⚬ B
  def uncurry[A, B, C](f: A -⚬ (B =⚬ C)): (A |*| B) -⚬ C =
    andThen(par(f, id[B]), eval[B, C])

  def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B])
  def unliftEither[A, B]: (Val[A] |+| Val[B]) -⚬ Val[Either[A, B]]

  def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B])
  def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)]

  /** Lifts an ordinary Scala function to a linear function on [[Val]]s. */
  def liftV[A, B](f: A => B): Val[A] -⚬ Val[B]

  /** Lifts an ordinary Scala function to a linear function on demands, in opposite direction. */
  def liftN[A, B](f: A => B): Neg[B] -⚬ Neg[A]

  def const[A](a: A): One -⚬ Val[A]

  def discard[A]: Val[A] -⚬ One

  def dup[A]: Val[A] -⚬ (Val[A] |*| Val[A]) =
    andThen(
      liftV[A, (A, A)](a => (a, a)),
      liftPair
    )

  def rec[A, B](f: (A -⚬ B) => (A -⚬ B)): A -⚬ B

  /** Unpacks one level of a recursive type definition. */
  def unpack[F[_]]: Rec[F] -⚬ F[Rec[F]]

  /** Hides one level of a recursive type definition. */
  def pack[F[_]]: F[Rec[F]] -⚬ Rec[F]

  /** Evidence that `A` is dual to `B`.
    * It must hold that `eliminate ⚬ introduce = id`.
    */
  trait Dual[A, B] {
    /** Creates a pair of dual entities from nothing. */
    def introduce: One -⚬ (A |*| B)

    /** Annihilates a pair of dual entities. */
    def eliminate: (A |*| B) -⚬ One
  }

  implicit def choiceEitherDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A |&| B, Ȧ |+| Ḃ]

  implicit def valNegDuality[A]: Dual[Val[A], Neg[A]]

  // TODO: weaken to `(Dual[A, Ȧ], One -⚬ B, One -⚬ C) => One -⚬ (A =⚬ B |*| Ȧ =⚬ C)`?
  implicit def functionDuality[A, B, Ȧ, Ḃ](implicit a: Dual[A, Ȧ], b: Dual[B, Ḃ]): Dual[A =⚬ B, Ȧ =⚬ Ḃ]

  /** If `A` is dual to `B`, then `F[A]` is dual to `G[B]`. */
  trait Dual1[F[_], G[_]] {
    def apply[A, Ā]: Dual[A, Ā] => Dual[F[A], G[Ā]]
  }

  /** If `F[A]` is dual to `G[B]` for all dual pairs `A`, `B`, then `Rec[F]` is dual to `Rec[G]`. */
  def dualRec[F[_], G[_]](ev: Dual1[F, G]): Dual[Rec[F], Rec[G]]

  /** Witnesses that `A` has an intrinsic notion of completion.
    * [[checkCompleted]] can be used to test whether a `Completive` object has completed.
    * [[race]] can be used to watch for which of two `Completive` objects completes first.
    */
  type Completive[A]

  implicit def completiveVal[A]: Completive[Val[A]]

  implicit def completivePlus[A, B]: Completive[A |+| B]

  def checkCompleted[A: Completive]: A -⚬ (A |+| A)

  /** Waits for completion of either of the two components of the concurrent product `A |*| B`.
    * If `A` completes first, returns left, if `B` first, returns right.
    * It is biased to the left: if both `A` and `B` have been completed by the time of inquiry, returns left.
    */
  def race[A: Completive, B: Completive]: (A |*| B) -⚬ ((A |*| B) |+| (A |*| B))

  /** Witnesses that `A` has an intrinsic notion of making a request request.
    * [[selectRequestedOrNot]] can be used to test whether a `Requisitive` object has made a request already.
    * [[select]] can be used to detect which of two `Selectable` objects made its request first.
    */
  type Requisitive[A]

  implicit def requisitiveNeg[A]: Requisitive[Neg[A]]

  implicit def requisitiveChoice[A, B]: Requisitive[A |&| B]

  def selectRequestedOrNot[A: Requisitive]: (A |&| A) -⚬ A

  /** Given a choice of two versions of `A |*| B`, selects one based on which component of the returned concurrent
    * product makes its request first: if `A` makes the request first, selects the left version, if `B` makes
    * the request first, selects the right version.
    * It is biased to the left: if both components of the result have made their request by the time of inquiry,
    * selects the left version of the input.
    */
  def select[A: Requisitive, B: Requisitive]: ((A |*| B) |&| (A |*| B)) -⚬ (A |*| B)
}