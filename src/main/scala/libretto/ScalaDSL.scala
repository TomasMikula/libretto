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
  def liftV[A, B](f: A => B): Val[A] -⚬ Val[B]

  /** Lifts an ordinary Scala function to a linear function on demands, in opposite direction. */
  def liftN[A, B](f: A => B): Neg[B] -⚬ Neg[A]

  def constVal[A](a: A): Done -⚬ Val[A]
  def constNeg[A](a: A): Neg[A] -⚬ Need

  def neglect[A]: Val[A] -⚬ Done
  def inflate[A]: Need -⚬ Neg[A]

  def dup[A]: Val[A] -⚬ (Val[A] |*| Val[A]) =
    andThen(
      liftV[A, (A, A)](a => (a, a)),
      liftPair
    )
}
