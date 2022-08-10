package libretto.testing

import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}
import libretto.{ScalaBridge, ScalaExecutor, StarterKit}
import libretto.testing.ScalaTestExecutor.ExecutionParam.Instantiation
import libretto.testing.ScalaTestExecutor.ScalaTestKitFromBridge

object StarterTestExecutor {

  private class StarterTestKitFromBridge[Bridge <: ScalaBridge.Of[StarterKit.dsl.type]](
    bridge: Bridge,
  ) extends ScalaTestExecutor.ScalaTestKitFromBridge[StarterKit.dsl.type, Bridge](StarterKit.dsl, bridge)

  def fromExecutor(
    exec: ScalaExecutor.OfDsl[StarterKit.dsl.type],
  ): TestExecutor[StarterTestKit] =
    new TestExecutor[StarterTestKit] {
      override val name: String =
        StarterTestExecutor.getClass.getCanonicalName

      override val testKit: ScalaTestKitFromBridge[StarterKit.dsl.type, exec.bridge.type] =
        new ScalaTestKitFromBridge(StarterKit.dsl, exec.bridge)

      import testKit.{ExecutionParam, Outcome}
      import testKit.dsl._
      import testKit.probes.Execution

      override def runTestCase[O, P, Y](
        body: Done -⚬ O,
        params: ExecutionParam[P],
        conduct: (exn: Execution) ?=> (exn.OutPort[O], P) => Outcome[Y],
        postStop: Y => Outcome[Unit],
      ): TestResult[Unit] = {
        val p: Instantiation[P, exec.ExecutionParam] =
          ScalaTestExecutor.ExecutionParam.instantiate(params)(using exec.ExecutionParam)

        TestExecutor
          .usingExecutor(exec)
          .runTestCase[O, p.X, Y](
            body,
            p.px,
            (port, x) => Outcome.toAsyncTestResult(conduct(port, p.get(x))),
            postStop andThen Outcome.toAsyncTestResult,
          )
      }

      override def runTestCase(body: () => Outcome[Unit]): TestResult[Unit] =
        TestExecutor
          .usingExecutor(exec)
          .runTestCase(() => Outcome.toAsyncTestResult(body()))
    }

  def fromJavaExecutors(
    scheduler: ScheduledExecutorService,
    blockingExecutor: ExecutorService,
  ): TestExecutor[StarterTestKit] = {
    val executor0: libretto.ScalaExecutor.OfDsl[StarterKit.dsl.type] =
      StarterKit.executor(blockingExecutor)(scheduler)

    fromExecutor(executor0)
  }

  lazy val global: TestExecutor[StarterTestKit] =
    fromJavaExecutors(
      scheduler        = Executors.newScheduledThreadPool(4),
      blockingExecutor = Executors.newCachedThreadPool(),
    )
}
