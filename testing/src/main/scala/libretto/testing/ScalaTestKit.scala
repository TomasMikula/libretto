package libretto.testing

import libretto.{CoreLib, ScalaBridge, ScalaDSL}
import libretto.testing.TestKit.dsl
import libretto.util.Monad.syntax._

trait ScalaTestKit extends TestKitWithManualClock {
  override val dsl: ScalaDSL
  override val probes: ScalaBridge.Of[dsl.type]

  import dsl._
  import probes.Execution

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

  def expectVal[A](using exn: Execution)(port: exn.OutPort[Val[A]]): Outcome[A] =
    Outcome.asyncTestResult(
      exn.OutPort.awaitVal(port).map {
        case Left(e)  => TestResult.crash(e)
        case Right(a) => TestResult.success(a)
      }
    )
}

object ScalaTestKit extends ScalaTestKitOps

trait ScalaTestKitOps extends TestKitOps {
  def failure[A](using kit: ScalaTestKit)(msg: String): dsl.-⚬[dsl.Done, kit.Assertion[A]] =
    kit.failure(msg)

  def assertLeft[A, B](using kit: ScalaTestKit)(
    ifRight: dsl.-⚬[B, dsl.Done],
    msg: String = "Expected Left, was Right",
  ): dsl.-⚬[dsl.|+|[A, B], kit.Assertion[A]] =
    kit.assertLeft(ifRight, msg)

  def assertRight[A, B](using kit: ScalaTestKit)(
    ifLeft: dsl.-⚬[A, dsl.Done],
    msg: String = "Expected Right, was Left",
  ): dsl.-⚬[dsl.|+|[A, B], kit.Assertion[B]] =
    kit.assertRight(ifLeft, msg)

  def leftOrCrash[A, B](using kit: ScalaTestKit)(msg: String = "Expected Left, was Right"): dsl.-⚬[dsl.|+|[A, B], A] =
    kit.leftOrCrash(msg)

  def rightOrCrash[A, B](using kit: ScalaTestKit)(msg: String = "Expected Right, was Left"): dsl.-⚬[dsl.|+|[A, B], B] =
    kit.rightOrCrash(msg)

  def assertEquals[A](using kit: ScalaTestKit)(expected: A): dsl.-⚬[dsl.Val[A], kit.Assertion[dsl.Done]] =
    kit.assertEquals(expected)

  def expectVal[A](using kit: ScalaTestKit, exn: kit.probes.Execution)(port: exn.OutPort[dsl.Val[A]]): kit.Outcome[A] =
    kit.expectVal(port)
}
