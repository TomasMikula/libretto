package libretto.testing

import java.util.concurrent.{ExecutorService, ScheduledExecutorService}
import libretto.{ScalaExecutor, StarterExecutor, StarterKit}

object StarterTestExecutor {
  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[StarterTestKit] = {
    val executor0: libretto.ScalaExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    ScalaTestExecutor.fromExecutor(executor0)
  }

  val defaultFactory: TestExecutor.Factory[StarterTestKit] =
    ScalaTestExecutor.defaultFactory(StarterExecutor.defaultFactory)

  lazy val global: TestExecutor[StarterTestKit] =
    defaultFactory.access(defaultFactory.create())
}
