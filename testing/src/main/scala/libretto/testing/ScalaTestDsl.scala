package libretto.testing

import libretto.{CoreLib, ScalaBridge, ScalaDSL}
import libretto.{testing => lt}
import libretto.util.Monad.syntax._

trait ScalaTestDsl extends TestDsl {
  override val dsl: ScalaDSL
  override val probes: ScalaBridge.Of[dsl.type, F]

  import dsl._
  import probes.{OutPort}

  private lazy val coreLib = CoreLib(dsl)
  import coreLib._

  def assertEquals[A](expected: A): Val[A] -⚬ TestResult[Done] =
    mapVal[A, Either[Unit, Unit]](a => if (a == expected) Right(()) else Left(()))
      .>( dsl.liftEither )
      .>( either(neglect > failure, neglect > success) )

  def expectVal[A](port: OutPort[Val[A]]): Outcome[A] =
    Outcome(
      probes.awaitVal(port).map {
        case Left(e)  => lt.TestResult.crash(e)
        case Right(a) => lt.TestResult.success(a)
      }
    )
}
