package libretto.testing

import libretto.{CoreLib, ScalaDSL}

trait ScalaTestDsl extends TestDsl {
  override val dsl: ScalaDSL

  import dsl._

  private lazy val coreLib = CoreLib(dsl)
  import coreLib._

  def assertEquals[A](expected: A): Val[A] -⚬ TestResult =
    mapVal[A, Either[Unit, Unit]](a => if (a == expected) Right(()) else Left(()))
      .>( dsl.liftEither )
      .>( either(neglect > failure, neglect > success) )
}
