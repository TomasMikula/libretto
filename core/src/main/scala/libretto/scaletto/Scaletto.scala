package libretto.scaletto

import libretto.CoreLib
import libretto.crash.CrashDSL
import libretto.timer.TimerDSL
import libretto.invert.InvertDSL
import libretto.lambda.util.SourcePos
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration
import scala.reflect.TypeTest

/** Supports manipulating Scala values via pure Scala functions.
  * Also extends [[InvertDSL]] (and thus [[ClosedDSL]]), [[TimerDSL]] and [[CrashDSL]],
  * since these are expected to be possible on a target platform that already supports Scala functions.
  */
trait Scaletto extends TimerDSL with CrashDSL with InvertDSL {
  /** Scala value of type `A`.
    *
    * Somewhat analogous to [[scala.concurrent.Future]].
    */
  type Val[A]

  /** Demand for a Scala value of type `A`.
    *
    * Somewhat analogous to [[scala.concurrent.Promise]]
    */
  type Neg[A] = -[Val[A]]

  /** Resource that is a Scala object of type [[A]].
    * Unlike [[Val]], a resource can be mutable, cannot in general be [[neglect]]ed or [[dup]]licated, and is
    * automatically cleaned-up in case of crash.
    *
    * It is recommended to define custom opaque type aliases of resources, such as
    *
    * ```
    * opaque type Input = Res[java.io.InputStream]
    * ```
    */
  type Res[A]

  override val UInt31: UInt31Scaletto

  trait UInt31Scaletto extends UInt31s {
    def fromInt: Val[Int] -⚬ UInt31
    def toInt: UInt31 -⚬ Val[Int]
  }

  type ScalaFun[A, B]
  val ScalaFun: ScalaFuns

  trait ScalaFuns {
    def apply[A, B](f: A => B): ScalaFun[A, B]
    def blocking[A, B](f: A => B): ScalaFun[A, B]
    def async[A, B](f: A => Async[B]): ScalaFun[A, B]

    def adapt[A, B, Z, C](f: ScalaFun[A, B])(pre: Z => A, post: B => C): ScalaFun[Z, C]
    def adaptWith[A, B, Z, P, C](f: ScalaFun[A, B])(pre: Z => (P, A), post: (P, B) => C): ScalaFun[Z, C]
    def eval[A, B]: ScalaFun[(ScalaFun[A, B], A), B]
  }

  extension [A, B](f: ScalaFun[A, B]) {
    def adapt[Z, C](pre: Z => A, post: B => C): ScalaFun[Z, C] =
      ScalaFun.adapt(f)(pre, post)

    def adaptPre[Z](pre: Z => A): ScalaFun[Z, B] =
      ScalaFun.adapt(f)(pre, identity)

    def adaptPost[C](post: B => C): ScalaFun[A, C] =
      ScalaFun.adapt(f)(identity, post)

    def adaptWith[Z, P, C](pre: Z => (P, A), post: (P, B) => C): ScalaFun[Z, C] =
      ScalaFun.adaptWith(f)(pre, post)
  }

  private val lib = CoreLib(this)
  import lib.*

  /** Creates an entangled pair of demand ([[Neg]]) and supply ([[Val]]) such that when the demand is fulfilled
    * with a value, that value will be produced by the supply.
    */
  def promise[A]: One -⚬ (Neg[A] |*| Val[A]) =
    forevert[Val[A]]

  /** Uses the value (eventually) produced by [[Val]] to satisfy the demand of [[Neg]]. */
  def fulfill[A]: (Val[A] |*| Neg[A]) -⚬ One =
    backvert[Val[A]]

  def liftEither[A, B]: Val[Either[A, B]] -⚬ (Val[A] |+| Val[B])
  def unliftEither[A, B]: (Val[A] |+| Val[B]) -⚬ Val[Either[A, B]] =
    either(mapVal(Left(_)), mapVal(Right(_)))

  def liftPair[A, B]: Val[(A, B)] -⚬ (Val[A] |*| Val[B])
  def unliftPair[A, B]: (Val[A] |*| Val[B]) -⚬ Val[(A, B)]

  def liftNegPair[A, B]: Neg[(A, B)] -⚬ (Neg[A] |*| Neg[B]) =
    introFst(parFromOne(promise[A], promise[B]) > IXI > snd(unliftPair)) > assocLR > elimSnd(fulfill)

  def unliftNegPair[A, B]: (Neg[A] |*| Neg[B]) -⚬ Neg[(A, B)] =
    introFst(promise[(A, B)] > snd(liftPair)) > assocLR > elimSnd(IXI > parToOne(fulfill, fulfill))

  def mapVal[A, B](f: ScalaFun[A, B]): Val[A] -⚬ Val[B]

  /** Lifts an ordinary Scala function to a linear function on [[Val]]s. */
  def mapVal[A, B](f: A => B): Val[A] -⚬ Val[B] =
    mapVal(ScalaFun(f))

  /** Lifts an ordinary Scala function to a linear function on demands, in opposite direction. */
  def contramapNeg[A, B](f: A => B): Neg[B] -⚬ Neg[A] =
    contrapositive(mapVal(f))

  def constVal[A](a: A): Done -⚬ Val[A]
  def constNeg[A](a: A): Neg[A] -⚬ Need

  transparent inline def constVal[A]: Done -⚬ Val[A] =
    constVal(scala.compiletime.constValue[A])

  transparent inline def constNeg[A]: Neg[A] -⚬ Need =
    constNeg(scala.compiletime.constValue[A])

  def neglect[A]: Val[A] -⚬ Done
  def inflate[A]: Need -⚬ Neg[A] =
    introFst(promise[A] > snd(neglect)) > assocLR > elimSnd(rInvertSignal)

  def notifyVal[A]: Val[A] -⚬ (Ping |*| Val[A])
  def notifyNeg[A]: (Pong |*| Neg[A]) -⚬ Neg[A]

  def dup[A]: Val[A] -⚬ (Val[A] |*| Val[A]) =
    mapVal[A, (A, A)](a => (a, a)) > liftPair

  def dupNeg[A]: (Neg[A] |*| Neg[A]) -⚬ Neg[A] =
    unliftNegPair[A, A] > contramapNeg(a => (a, a))

  def switchVal[A, R](
    a: $[Val[A]],
    cases: ValSwitch.Cases[A, A, R],
  )(pos: SourcePos)(using
    LambdaContext,
  ): $[R]

  def switch[A](using pos: SourcePos)(a: $[Val[A]])(using LambdaContext): ValSwitchInit[A] =
    ValSwitchInit(a, pos)

  def delay: Val[FiniteDuration] -⚬ Done

  def delayNeed: Need -⚬ Neg[FiniteDuration] =
    id                                         [                                                    Need  ]
      .>(introFst(promise[FiniteDuration])) .to[ (Neg[FiniteDuration] |*|  Val[FiniteDuration]) |*| Need  ]
      .>(assocLR)                           .to[  Neg[FiniteDuration] |*| (Val[FiniteDuration]  |*| Need) ]
      .>.snd.fst(delay)                     .to[  Neg[FiniteDuration] |*| (  Done               |*| Need) ]
      .>(elimSnd(rInvertSignal))            .to[  Neg[FiniteDuration]                                     ]

  override def delay(d: FiniteDuration): Done -⚬ Done =
    constVal(d) > delay

  def acquire[A, R, B](
    acquire: ScalaFun[A, (R, B)],
    release: Option[ScalaFun[R, Unit]],
  ): Val[A] -⚬ (Res[R] |*| Val[B])

  /** Acquires a resource of type [[R]].
    *
    * @param acquire
    * @param release called to release the resource in case of a crash. `None` means no cleanup is needed
    * @tparam A parameters of the `acquire` function
    * @tparam R type of the resource
    * @tparam B additional data produced by acquiring the resource
    */
  def acquire[A, R, B](
    acquire: A => (R, B),
    release: Option[R => Unit],
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    this.acquire(ScalaFun(acquire), release.map(ScalaFun(_)))

  def acquireAsync[A, R, B](
    acquire: A => Async[(R, B)],
    release: Option[R => Async[Unit]],
  ): Val[A] -⚬ (Res[R] |*| Val[B]) =
    this.acquire(ScalaFun.async(acquire), release.map(ScalaFun.async(_)))

  /** Acquires a resource of type [[R]]. Might fail with an error of type [[E]].
    *
    * @param acquire
    * @param release called to release the resource in case of a crash. `None` means no cleanup is needed
    * @tparam A parameters of the `acquire` function
    * @tparam R type of the resource
    * @tparam B additional data produced by acquiring the resource
    * @tparam E type of the error
    */
  def tryAcquire[A, R, B, E](
    acquire: A => Either[E, (R, B)],
    release: Option[R => Unit],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B])) =
    tryAcquire(
      ScalaFun(acquire),
      release.map(ScalaFun(_)),
    )

  def tryAcquire[A, R, B, E](
    acquire: ScalaFun[A, Either[E, (R, B)]],
    release: Option[ScalaFun[R, Unit]],
  ): Val[A] -⚬ (Val[E] |+| (Res[R] |*| Val[B]))

  /** Releases a resource using the `release` function registered during resource acquisition. */
  def release[R]: Res[R] -⚬ Done

  def releaseWith[R, A, B](f: ScalaFun[(R, A), B]): (Res[R] |*| Val[A]) -⚬ Val[B]

  /** Releases a resource using the given function. The `release` function previously registered during resource
    * acquisition is not used.
    *
    * @param f the release function
    * @tparam R type of the resource
    * @tparam A additional parameter of the release function
    * @tparam B additional data produced by the release function
    */
  def release[R, A, B](f: (R, A) => B): (Res[R] |*| Val[A]) -⚬ Val[B] =
    releaseWith(ScalaFun(f.tupled))

  def releaseAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ Val[B] =
    releaseWith(ScalaFun.async(f.tupled))

  def effect[R, A, B](f: ScalaFun[(R, A), B]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B])

  /** Performs a (potentially) effectful operation on a resource, producing some output.
    *
    * @param f the effectful operation
    * @tparam R type of the resource
    * @tparam A additional parameter of the operation
    * @tparam B additional output of the operation
    */
  def effect[R, A, B](f: (R, A) => B): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    effect(ScalaFun(f.tupled))

  def effectAsync[R, A, B](f: (R, A) => Async[B]): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| Val[B]) =
    effect(ScalaFun.async(f.tupled))

  def effectWr[R, A](f: ScalaFun[(R, A), Unit]): (Res[R] |*| Val[A]) -⚬ Res[R]

  /** Variant of [[effect]] that does not produce output in addition to performing the effect.
    * Can be viewed as ''wr''iting an [[A]] into the resource.
    */
  def effectWr[R, A](f: (R, A) => Unit): (Res[R] |*| Val[A]) -⚬ Res[R] =
    effectWr(ScalaFun(f.tupled))

  def effectWrAsync[R, A](f: (R, A) => Async[Unit]): (Res[R] |*| Val[A]) -⚬ Res[R] =
    effectWr(ScalaFun.async(f.tupled))

  def tryEffectAcquire[R, A, S, B, E](
    f: ScalaFun[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFun[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Res[R] |*| (Val[E] |+| (Res[S] |*| Val[B])))

  /** Transforms a resource into a resource of (possibly) different type.
    *
    * @param f the transformation function. It receives the input resource and additional input of type [[A]].
    *          It returns the new resource and additional output of type [[B]].
    * @param release called to release the new resource in case of a crash. `None` means no cleanup is needed
    * @tparam R type of the input resource
    * @tparam A additional parameter of the transformation
    * @tparam S type of the output resource
    * @tparam B additional output of the transformation
    */
  def transformResource[R, A, S, B](
    f: (R, A) => (S, B),
    release: Option[S => Unit],
  ): (Res[R] |*| Val[A]) -⚬ (Res[S] |*| Val[B]) =
    transformResourceAsync(
      (r, a) => Async.now(f(r, a)),
      release.map(_ andThen Async.now),
    )

  def transformResourceAsync[R, A, S, B](
    f: (R, A) => Async[(S, B)],
    release: Option[S => Async[Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Res[S] |*| Val[B]) =
    tryTransformResourceAsync[R, A, S, B, Nothing](
      (r, a) => f(r, a).map(Right(_)),
      release,
    )                                       .to[ Val[Nothing] |+| (Res[S] |*| Val[B]) ]
      > either(anyResourceFromNothing, id)  .to[                   Res[S] |*| Val[B]  ]

  def tryTransformResource[R, A, S, B, E](
    f: ScalaFun[(R, A), Either[E, (S, B)]],
    release: Option[ScalaFun[S, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B]))

  /** Transforms a resource into a resource of (possibly) different type. Might fail with an error of type [[E]].
    *
    * @param f the transformation function. It receives the input resource and additional input of type [[A]].
    *          It returns either an error of type [[E]] or the new resource and additional output of type [[B]].
    *          In case the transformation results in an error, the original resource is ''not'' released automatically—
    *          the passing of the original resource `R` to the transformation function `f` indicates transfer of
    *          responsibility for the resource to the function `f`.
    * @param release called to release the new resource in case of a crash. `None` means no cleanup is needed
    * @tparam R type of the input resource
    * @tparam A additional parameter of the transformation
    * @tparam S type of the output resource
    * @tparam B additional output of the transformation
    * @tparam E type of the error
    */
  def tryTransformResource[R, A, S, B, E](
    f: (R, A) => Either[E, (S, B)],
    release: Option[S => Unit],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    tryTransformResource(
      ScalaFun(f.tupled),
      release.map(ScalaFun(_)),
    )

  def tryTransformResourceAsync[R, A, S, B, E](
    f: (R, A) => Async[Either[E, (S, B)]],
    release: Option[S => Async[Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| (Res[S] |*| Val[B])) =
    tryTransformResource(
      ScalaFun.async(f.tupled),
      release.map(ScalaFun.async(_)),
    )

  def splitResource[R, A, S, T, B](
    f: ScalaFun[(R, A), (S, T, B)],
    release1: Option[ScalaFun[S, Unit]],
    release2: Option[ScalaFun[T, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ ((Res[S] |*| Res[T]) |*| Val[B]) =
    trySplitResource(
      ScalaFun.adapt(f)(identity[(R, A)], Right[Nothing, (S, T, B)]),
      release1,
      release2,
    ) > either(anyTwoResourcesFromNothing, id)

  def splitResource[R, A, S, T, B](
    f: (R, A) => (S, T, B),
    release1: Option[S => Unit],
    release2: Option[T => Unit],
  ): (Res[R] |*| Val[A]) -⚬ ((Res[S] |*| Res[T]) |*| Val[B]) =
    splitResource(
      ScalaFun(f.tupled),
      release1.map(ScalaFun(_)),
      release2.map(ScalaFun(_)),
    )

  def splitResourceAsync[R, A, S, T, B](
    f: (R, A) => Async[(S, T, B)],
    release1: Option[S => Async[Unit]],
    release2: Option[T => Async[Unit]],
  ): (Res[R] |*| Val[A]) -⚬ ((Res[S] |*| Res[T]) |*| Val[B]) =
      splitResource(
        ScalaFun.async(f.tupled),
        release1.map(ScalaFun.async(_)),
        release2.map(ScalaFun.async(_)),
      )

  def trySplitResource[R, A, S, T, B, E](
    f: ScalaFun[(R, A), Either[E, (S, T, B)]],
    release1: Option[ScalaFun[S, Unit]],
    release2: Option[ScalaFun[T, Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B]))

  def trySplitResource[R, A, S, T, B, E](
    f: (R, A) => Either[E, (S, T, B)],
    release1: Option[S => Unit],
    release2: Option[T => Unit],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])) =
    trySplitResource(
      ScalaFun(f.tupled),
      release1.map(ScalaFun(_)),
      release2.map(ScalaFun(_)),
    )

  def trySplitResourceAsync[R, A, S, T, B, E](
    f: (R, A) => Async[Either[E, (S, T, B)]],
    release1: Option[S => Async[Unit]],
    release2: Option[T => Async[Unit]],
  ): (Res[R] |*| Val[A]) -⚬ (Val[E] |+| ((Res[S] |*| Res[T]) |*| Val[B])) =
    trySplitResource(
      ScalaFun.async(f.tupled),
      release1.map(ScalaFun.async(_)),
      release2.map(ScalaFun.async(_)),
    )


  private def anyResourceFromNothing[R, B]: Val[Nothing] -⚬ (Res[R] |*| Val[B])=
    acquire(x => x, release = None)

  private def anyTwoResourcesFromNothing[S, T, B]: Val[Nothing] -⚬ ((Res[S] |*| Res[T]) |*| Val[B]) =
    dup[Nothing]                                                                          .to[       Val[Nothing]        |*|          Val[Nothing]           ]
      .>( par(anyResourceFromNothing[S, Nothing], anyResourceFromNothing[T, Nothing]) )   .to[ (Res[S] |*| Val[Nothing]) |*| (   Res[T]    |*| Val[Nothing]) ]
      .>( IXI )                                                                           .to[ (Res[S] |*|    Res[T]   ) |*| (Val[Nothing] |*| Val[Nothing]) ]
      .>( par(id, unliftPair > mapVal(_._1)) )                                            .to[ (Res[S] |*|    Res[T]   ) |*|             Val[B]              ]

  /** Executes a potentially blocking operation.
   *  The runtime will ensure that the blocking operation does not impede
   *  any of the concurrently happening non-blocking computations.
   */
  def blocking[A, B](f: A => B): Val[A] -⚬ Val[B] =
    mapVal(ScalaFun.blocking(f))

  /** Prints the given message to the console, without creating an obligation to await. */
  def debugPrint(msg: String): Ping -⚬ One

  def constantVal[A](a: A)(using SourcePos, LambdaContext): $[Val[A]] =
    constant(done) > constVal(a)

  def tuple[A, B](a: $[Val[A]], b: $[Val[B]])(using
    SourcePos,
    LambdaContext,
  ): $[Val[(A, B)]] =
    (a |*| b) > unliftPair

  def tuple[A, B, C](a: $[Val[A]], b: $[Val[B]], c: $[Val[C]])(using
    SourcePos,
    LambdaContext,
  ): $[Val[(A, B, C)]] =
    tuple(tuple(a, b), c) > mapVal { case ((a, b), c) => (a, b, c) }

  def tuple[A, B, C, D](a: $[Val[A]], b: $[Val[B]], c: $[Val[C]], d: $[Val[D]])(using
    SourcePos,
    LambdaContext,
  ): $[Val[(A, B, C, D)]] =
    tuple(tuple(a, b), tuple(c, d)) > mapVal { case ((a, b), (c, d)) => (a, b, c, d) }

  def tuple[A, B, C, D, E](a: $[Val[A]], b: $[Val[B]], c: $[Val[C]], d: $[Val[D]], e: $[Val[E]])(using
    SourcePos,
    LambdaContext,
  ): $[Val[(A, B, C, D, E)]] =
    tuple(tuple(a, b, c), tuple(d, e)) > mapVal { case ((a, b, c), (d, e)) => (a, b, c, d, e) }

  def tuple[A, B, C, D, E, F](a: $[Val[A]], b: $[Val[B]], c: $[Val[C]], d: $[Val[D]], e: $[Val[E]], f: $[Val[F]])(using
    SourcePos,
    LambdaContext,
  ): $[Val[(A, B, C, D, E, F)]] =
    tuple(tuple(a, b, c), tuple(d, e, f)) > mapVal { case ((a, b, c), (d, e, f)) => (a, b, c, d, e, f) }

  class ValSwitchInit[A](a: $[Val[A]], pos: SourcePos)(using LambdaContext) {
    def Case[A0 <: A](using tt: TypeTest[A, A0], casePos: SourcePos): ValSwitchInitCase[A, A0] =
      ValSwitchInitCase[A, A0](a, pos, tt, casePos)
  }

  class ValSwitchInitCase[A, A0 <: A](a: $[Val[A]], pos: SourcePos, tt: TypeTest[A, A0], casePos: SourcePos)(using LambdaContext) {
    def apply[R](f: LambdaContext ?=> $[Val[A0]] => $[R]): ValSwitch[A, A0, R] =
      ValSwitch(a, pos, ValSwitch.FirstCase(tt, f, casePos))
  }

  /**
   *
   * @tparam A type of the scrutinee (the value to match on)
   * @tparam A0 subtype of A covered so far
   * @tparam R result type that each case must produce
   */
  class ValSwitch[A, A0, R](a: $[Val[A]], pos: SourcePos, cases: ValSwitch.Cases[A, A0, R])(using LambdaContext) {
    def endswitch(using ev: A0 =:= A): $[R] =
      switchVal[A, R](a, ev.substituteCo[[a] =>> ValSwitch.Cases[A, a, R]](cases))(pos)

    def Case[A1 <: A](using tt: TypeTest[A, A1], pos: SourcePos)(
      f: LambdaContext ?=> $[Val[A1]] => $[R],
    ): ValSwitch[A, A0 | A1, R] =
      ValSwitch(a, pos, ValSwitch.NextCase(cases, tt, f, pos))
  }

  object ValSwitch {
    sealed trait Cases[A, A0, R]

    class FirstCase[A, A0, R](
      val typeTest: TypeTest[A, A0],
      val f: LambdaContext ?=> $[Val[A0]] => $[R],
      val pos: SourcePos,
    ) extends Cases[A, A0, R]

    class NextCase[A, A0, A1, R](
      val base: Cases[A, A0, R],
      val typeTest: TypeTest[A, A1],
      val f: LambdaContext ?=> $[Val[A1]] => $[R],
      val pos: SourcePos,
    ) extends Cases[A, A0 | A1, R]
  }

  /** Returns the size of the given program, in further unspecified units.
   * Useful only for approximate relative comparisons.
   */
  def sizeOf[A, B](f: A -⚬ B): Long
}
