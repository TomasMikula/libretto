package libretto.scaletto

import libretto.Executor
import libretto.ExecutionParams

trait ScalettoExecutor extends Executor { self =>
  override type Dsl <: Scaletto
  override type Bridge <: ScalettoBridge.Of[dsl.type]

  override val ExecutionParam: ExecutionParams.WithScheduler[ExecutionParam]

  override def narrow: ScalettoExecutor.Of[dsl.type, bridge.type] =
    new ScalettoExecutor {
      override type Dsl = self.dsl.type
      override type Bridge = self.bridge.type

      export self.{dsl, bridge, ExecutionParam, execute, cancel}
    }
}

object ScalettoExecutor {
  type OfDsl[DSL <: Scaletto] = ScalettoExecutor { type Dsl = DSL }

  type Of[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL]] =
    ScalettoExecutor { type Dsl = DSL; type Bridge = BRIDGE }

  trait Factory extends Executor.Factory {
    override type Dsl <: Scaletto
    override type Bridge <: ScalettoBridge.Of[dsl.type]

    override def access(r: ExecutorResource): ScalettoExecutor.Of[dsl.type, bridge.type]
  }

  object Factory {
    type Of[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }

  private[libretto] val defaultFactory0: ScalettoExecutor.Factory.Of[StarterKit.dsl.type, StarterKit.bridge.type] =
    new ScalettoExecutor.Factory {
      import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}

      override type Dsl = StarterKit.dsl.type
      override type Bridge = StarterKit.bridge.type

      override val dsl = StarterKit.dsl
      override val bridge = StarterKit.bridge

      override type ExecutorResource =
        (ScheduledExecutorService, ExecutorService, ScalettoExecutor.Of[dsl.type, bridge.type])

      override def access(r: ExecutorResource): ScalettoExecutor.Of[dsl.type, bridge.type] =
        r._3

      override def create(): ExecutorResource = {
        val scheduler = Executors.newScheduledThreadPool(Runtime.getRuntime().availableProcessors())
        val blockingExecutor = Executors.newCachedThreadPool()
        val executor = StarterKit.executor(blockingExecutor)(scheduler)
        (scheduler, blockingExecutor, executor)
      }

      override def shutdown(r: ExecutorResource): Unit = {
        r._2.shutdownNow()
        r._1.shutdownNow()
      }
    }

  val defaultFactory: ScalettoExecutor.Factory =
    defaultFactory0
}
