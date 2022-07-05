package libretto.testing

import libretto.{CoreLib, ScalaBridge, ScalaDSL}
import libretto.util.Monad.syntax._

trait ScalaTestKit extends TestKit {
  override val dsl: ScalaDSL
  override val probes: ScalaBridge.Of[dsl.type, F]

  import dsl._
  import probes.OutPort

  private lazy val coreLib = CoreLib(dsl)
  import coreLib._

  def failure[A](msg: String): Done -⚬ Assertion[A]

  def assertLeft[A, B](
    ifRight: B -⚬ Done,
    msg: String = "Expected Left, was Right",
  ): (A |+| B) -⚬ Assertion[A] =
    either(success[A], ifRight > failure(msg))

  def assertRight[A, B](
    ifLeft: A -⚬ Done,
    msg: String = "Expected Right, was Left",
  ): (A |+| B) -⚬ Assertion[B] =
    either(ifLeft > failure(msg), success[B])

  def leftOrCrash[A, B](msg: String = "Expected Left, was Right"): (A |+| B) -⚬ A =
    |+|.signalR > either(id[A], crashWhenDone[B, A](msg))

  def rightOrCrash[A, B](msg: String = "Expected Right, was Left"): (A |+| B) -⚬ B =
    |+|.signalL > either(crashWhenDone[A, B](msg), id[B])

  def assertEquals[A](expected: A): Val[A] -⚬ Assertion[Done] =
    mapVal[A, Either[Unit, Unit]](a => if (a == expected) Right(()) else Left(()))
      .>( dsl.liftEither )
      .>( either(neglect > failure, neglect > success) )

  def expectVal[A](port: OutPort[Val[A]]): Outcome[A] =
    Outcome(
      OutPort.awaitVal(port).map {
        case Left(e)  => TestResult.crash(e)
        case Right(a) => TestResult.success(a)
      }
    )
}
