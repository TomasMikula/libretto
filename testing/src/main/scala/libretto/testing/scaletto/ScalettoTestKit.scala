package libretto.testing.scaletto

import libretto.CoreLib
import libretto.scaletto.{Scaletto, ScalettoBridge}
import libretto.testing.TestKit.dsl
import libretto.testing.{TestKitOps, TestKitWithManualClock, TestResult}

trait ScalettoTestKit extends TestKitWithManualClock {
  override type Dsl <: Scaletto

  override val bridge: ScalettoBridge.Of[dsl.type]

  import dsl.*
  import bridge.Execution

  private lazy val coreLib = CoreLib(dsl)
  import coreLib.*

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
      port.awaitVal().map {
        case Left(e)  => TestResult.crash(e)
        case Right(a) => TestResult.success(a)
      }
    )
}

object ScalettoTestKit extends ScalettoTestKitOps {
  type Of[DSL <: Scaletto] = ScalettoTestKit { type Dsl = DSL }
}

trait ScalettoTestKitOps extends TestKitOps {
  def failure[A](using kit: ScalettoTestKit)(msg: String): dsl.-⚬[dsl.Done, kit.Assertion[A]] =
    kit.failure(msg)

  def assertLeft[A, B](using kit: ScalettoTestKit)(
    ifRight: dsl.-⚬[B, dsl.Done],
    msg: String = "Expected Left, was Right",
  ): dsl.-⚬[dsl.|+|[A, B], kit.Assertion[A]] =
    kit.assertLeft(ifRight, msg)

  def assertRight[A, B](using kit: ScalettoTestKit)(
    ifLeft: dsl.-⚬[A, dsl.Done],
    msg: String = "Expected Right, was Left",
  ): dsl.-⚬[dsl.|+|[A, B], kit.Assertion[B]] =
    kit.assertRight(ifLeft, msg)

  def leftOrCrash[A, B](using kit: ScalettoTestKit)(msg: String = "Expected Left, was Right"): dsl.-⚬[dsl.|+|[A, B], A] =
    kit.leftOrCrash(msg)

  def rightOrCrash[A, B](using kit: ScalettoTestKit)(msg: String = "Expected Right, was Left"): dsl.-⚬[dsl.|+|[A, B], B] =
    kit.rightOrCrash(msg)

  def assertEquals[A](using kit: ScalettoTestKit)(expected: A): dsl.-⚬[dsl.Val[A], kit.Assertion[dsl.Done]] =
    kit.assertEquals(expected)

  def expectVal[A](using kit: ScalettoTestKit, exn: kit.bridge.Execution)(port: exn.OutPort[dsl.Val[A]]): kit.Outcome[A] =
    kit.expectVal(port)
}
