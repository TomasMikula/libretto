package libretto.scaletto

import libretto.Executor
import libretto.util.Scheduler

trait ScalettoExecutor extends Executor { self =>
  override val dsl: Scaletto
  override val bridge: ScalettoBridge.Of[dsl.type]

  val ExecutionParam: ScalettoExecutor.ExecutionParam[ExecutionParam]

  override def narrow: ScalettoExecutor.Of[dsl.type, bridge.type] =
    this
}

object ScalettoExecutor {
  type OfDsl[DSL <: Scaletto] = ScalettoExecutor {
    val dsl: DSL
  }

  type Of[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL]] =
    ScalettoExecutor {
      val dsl: DSL
      val bridge: BRIDGE
    }

  trait Factory extends Executor.Factory {
    override type Dsl <: Scaletto
    override type Bridge <: ScalettoBridge.Of[dsl.type]

    override def access(r: ExecutorResource): ScalettoExecutor.Of[dsl.type, bridge.type]
  }

  object Factory {
    type Of[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }

  trait ExecutionParam[P[_]]:
    def scheduler(s: Scheduler): P[Unit]

  val defaultFactory: ScalettoExecutor.Factory =
    libretto.scaletto.impl.futurebased.FutureExecutor.defaultFactory
}
