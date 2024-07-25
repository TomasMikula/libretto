package libretto.testing.scaletto

import libretto.scaletto.StarterKit
import libretto.testing.TestExecutor

object StarterTestExecutor {
  val defaultFactory: TestExecutor.Factory[StarterTestKit] =
    ScalettoTestExecutor.defaultFactory(StarterKit.executorFactory)

  lazy val global: TestExecutor[StarterTestKit] =
    defaultFactory.access(defaultFactory.create())
}
