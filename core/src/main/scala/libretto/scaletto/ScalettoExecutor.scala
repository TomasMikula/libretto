package libretto.scaletto

import libretto.{Executor, Scheduler}

trait ScalettoExecutor extends Executor { self =>
  override type Dsl <: Scaletto
  override type Bridge <: ScalettoBridge.Of[dsl.type]

  val ExecutionParam: ScalettoExecutor.ExecutionParam[ExecutionParam]

  override def narrow: ScalettoExecutor.Of[dsl.type, bridge.type] =
    new ScalettoExecutor {
      override type Dsl = self.dsl.type
      override type Bridge = self.bridge.type

      export self.{dsl, bridge, ExecutionParam, execute, cancel, watchForCancellation}
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

  trait ExecutionParam[P[_]]:
    def scheduler(s: Scheduler): P[Unit]

  val defaultFactory: ScalettoExecutor.Factory =
    libretto.scaletto.impl.futurebased.FutureExecutor.defaultFactory
}
