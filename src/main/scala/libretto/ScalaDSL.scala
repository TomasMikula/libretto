package libretto

/** Extension of [[CoreDSL]], [[TimerDSL]] and [[CrashDSL]] that adds support for manipulating Scala values via pure
  * Scala functions.
  */
trait ScalaDSL extends TimerDSL with CrashDSL {
  /** Scala value of type `A`.
    *
    * Somewhat analogous to [[scala.concurrent.Future]].
    */
  type Val[A]

  /** Demand for a Scala value of type `A`.
    *
    * Somewhat analogous to [[scala.concurrent.Promise]]
    */
  type Neg[A]
  
  /** Resource that is a Scala object of type [[A]].
    * Unlike [[Val]], a resource can be mutable, cannot in general be [[neglect]]ed or [[dup]]licated, and is
    * automatically cleaned-up in case of crash.
    * 
    * It is recommended to define custom opaque type aliases of resources, such as
    * 
    * {{{
    * opaque type Input = Res[java.io.InputStream]
    * }}}
    */
  type Res[A]

  private val lib = CoreLib(this)
  import lib._

  /** Creates an entangled pair of demand ([[Neg]]) and supply ([[Val]]) such that when the demand is fulfilled
    * with a value, that value will be produced by the supply.
    */
  def promise[A]: One -⚬ (Neg[A] |*| Val[A])

  /** Uses the value (eventually) produced by [[Val]] to satisfy the demand of [[Neg]]. */
  def fulfill[A]: (Val[A] |*| Neg[A]) -⚬ One

  def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B])
  def unliftEither[A, B]: (Val[A] |+| Val[B]) -⚬ Val[Either[A, B]]

  def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B])
  def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)]

  def liftNegPair[A, B]: Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B])
  def unliftNegPair[A, B]: (Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)]

  /** Lifts an ordinary Scala function to a linear function on [[Val]]s. */
  def mapVal[A, B](f: A => B): Val[A] -⚬ Val[B]

  /** Lifts an ordinary Scala function to a linear function on demands, in opposite direction. */
  def contramapNeg[A, B](f: A => B): Neg[B] -⚬ Neg[A]

  def constVal[A](a: A): Done -⚬ Val[A]
  def constNeg[A](a: A): Neg[A] -⚬ Need

  def neglect[A]: Val[A] -⚬ Done
  def inflate[A]: Need -⚬ Neg[A]

  def dup[A]: Val[A] -⚬ (Val[A] |*| Val[A]) =
    andThen(
      mapVal[A, (A, A)](a => (a, a)),
      liftPair
    )

  /** Create a resource that is just a (potentially) mutable value which does not need any cleanup.
    * 
    * @param init function that initializes the (potentially) mutable value from an immutable one.
    */
  def mVal[A, B](init: A => B): Val[A] -⚬ Res[B]

  /** Acquires a resource of type [[R]].
    * 
    * @param acquire 
    * @param release called to release the resource in case of a crash
    * @tparam A parameters of the `acquire` function
    * @tparam R type of the resource
    * @tparam B additional data produced by acquiring the resource
    */
  def acquire[A, R, B](
    acquire: A => (R, B),
    release: R => Unit,
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    acquireAsync(
      acquire andThen Async.now,
      release andThen Async.now,
    )
  
  def acquireAsync[A, R, B](
    acquire: A => Async[(R, B)],
    release: R => Async[Unit],
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    tryAcquireAsync[A, R, B, Nothing](
      a => acquire(a).map(Right(_)),
      release
    )                                       .to[ Val[Nothing] |+| (Res[R] |*| Val[B]) ]
      .either(anyResourceFromNothing, id)   .to[                   Res[R] |*| Val[B]  ]

  /** Acquires a resource of type [[R]]. Might fail with an error of type [[E]].
    *
    * @param acquire
    * @param release called to release the resource in case of a crash
    * @tparam A parameters of the `acquire` function
    * @tparam R type of the resource
    * @tparam B additional data produced by acquiring the resource
    * @tparam E type of the error
    */
  def tryAcquire[A, R, B, E](
    acquire: A => Either[E, (R, B)],
    release: R => Unit,
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])) =
    tryAcquireAsync(
      acquire andThen Async.now,
      release andThen Async.now,
    )
  
  def tryAcquireAsync[A, R, B, E](
    acquire: A => Async[Either[E, (R, B)]],
    release: R => Async[Unit],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B]))

  /** Releases a resource.
    * 
    * @param f the release function
    * @tparam R type of the resource
    * @tparam A additional parameter of the release function
    * @tparam B additional data produced by the release function
    */
  def release[R, A, B](f: (R, A) => B): (Res[R] |*| Val[A]) -⚬ Val[B] =
    releaseAsync((r, a) => Async.now(f(r, a)))

  def releaseAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ Val[B]

  /** Performs a (potentially) effectful operation on a resource. In addition to having an effect, the operation
    * produces additional output.
    * 
    * @param f the effectful operation
    * @tparam R type of the resource
    * @tparam A additional parameter of the operation
    * @tparam B additional output of the operation
    */
  def effect[R, A, B](f: (R, A) => (R, B)): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    effectAsync((r, a) => Async.now(f(r, a)))

  def effectAsync[R, A, B](f: (R, A) => Async[(R, B)]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B])
  
  /** Variant of [[effect]] that does not produce output in addition to performing the effect.
    * Can be viewed as ''wr''iting an [[A]] into the resource.
    */
  def effectWr[R, A](f: (R, A) => R): (Res[R] |*| Val[A]) -⚬ Res[R] =
    effectWrAsync((r, a) => Async.now(f(r, a)))
  
  def effectWrAsync[R, A](f: (R, A) => Async[R]): (Res[R] |*| Val[A]) -⚬ Res[R]

  /** Transforms a resource into a resource of (possibly) different type.
    * 
    * @param f the transformation function. It receives the input resource and additional input of type [[A]].
    *          It returns the new resource and additional output of type [[B]].
    * @param release called to release the new resource in case of a crash
    * @tparam R type of the input resource
    * @tparam A additional parameter of the transformation
    * @tparam S type of the output resource
    * @tparam B additional output of the transformation
    */
  def transformResource[R, A, S, B](
    f: (R, A) => (S, B),
    release: S => Unit,
  ): (Res[R] |*| Val[A]) -⚬ (Res[S] |*| Val[B]) =
    transformResourceAsync(
      (r, a) => Async.now(f(r, a)),
      s => Async.now(release(s)),
    )

  def transformResourceAsync[R, A, S, B](
    f: (R, A) => Async[(S, B)],
    release: S => Async[Unit],
  ): (Res[R] |*| Val[A]) -⚬ (Res[S] |*| Val[B]) =
    tryTransformResourceAsync[R, A, S, B, Nothing](
      (r, a) => f(r, a).map(Right(_)),
      release,
    )                                       .to[ Val[Nothing] |+| (Res[S] |*| Val[B]) ]
      .either(anyResourceFromNothing, id)   .to[                   Res[S] |*| Val[B]  ]

  /** Transforms a resource into a resource of (possibly) different type. Might fail with an error of type [[E]].
    *
    * @param f the transformation function. It receives the input resource and additional input of type [[A]].
    *          It returns either an error of type [[E]] or the new resource and additional output of type [[B]].
    *          In case the transformation results in an error, the original resource is ''not'' released automatically—
    *          the passing of the original resource `R` to the transformation function `f` indicates transfer of
    *          responsibility for the resource to the function `f`.
    * @param release called to release the new resource in case of a crash
    * @tparam R type of the input resource
    * @tparam A additional parameter of the transformation
    * @tparam S type of the output resource
    * @tparam B additional output of the transformation
    * @tparam E type of the error
    */
  def tryTransformResource[R, A, S, B, E](
    f: (R, A) => Either[E, (S, B)],
    release: S => Unit,
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    tryTransformResourceAsync(
      (r, a) => Async.now(f(r, a)),
      s => Async.now(release(s)),
    )

  def tryTransformResourceAsync[R, A, S, B, E](
    f: (R, A) => Async[Either[E, (S, B)]],
    release: S => Async[Unit],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B]))


  private def anyResourceFromNothing[R, B]: Val[Nothing] -⚬ (Res[R] |*| Val[B])=
    id                           [ Val[Nothing] ]
      .>(mapVal(x => x))      .to[ Val[(R, B)] ]
      .>(liftPair)            .to[ Val[R] |*| Val[B] ]
      .>.fst(mVal(identity))  .to[ Res[R] |*| Val[B] ]
}
