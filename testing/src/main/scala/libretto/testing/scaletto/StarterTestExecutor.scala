package libretto.testing.scaletto

import java.util.concurrent.{ExecutorService, ScheduledExecutorService}
import libretto.scaletto.{ScalettoExecutor, StarterKit}
import libretto.testing.TestExecutor

object StarterTestExecutor {
  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[StarterTestKit] = {
    val executor0: ScalettoExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    ScalettoTestExecutor.fromExecutor(executor0)
  }

  val defaultFactory: TestExecutor.Factory[StarterTestKit] =
    ScalettoTestExecutor.defaultFactory(StarterKit.executorFactory)

  lazy val global: TestExecutor[StarterTestKit] =
    defaultFactory.access(defaultFactory.create())
}
