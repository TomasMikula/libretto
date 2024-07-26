package libretto.scaletto

import libretto.CoreExecutor
import libretto.exec.{Executor, SupportsCustomScheduler}

trait ScalettoExecutor extends CoreExecutor { self =>
  override val dsl: Scaletto
  override val bridge: ScalettoBridge.Of[dsl.type]
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

  type Ofp[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL], P[_]] =
    Of[DSL, BRIDGE] { type ExecutionParam[A] = P[A] }

  trait Factory extends Executor.Factory {
    override type Dsl <: Scaletto
    override type Bridge <: ScalettoBridge.Of[dsl.type]

    override def access(r: ExecutorResource): ScalettoExecutor.Ofp[dsl.type, bridge.type, ExecutionParam]
  }

  object Factory {
    type Of[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }

    type Ofp[DSL <: Scaletto, BRIDGE <: ScalettoBridge.Of[DSL], P[_]] =
      Of[DSL, BRIDGE] { type ExecutionParam[A] = P[A] }
  }

  val defaultFactory: ScalettoExecutor.Factory =
    libretto.scaletto.impl.futurebased.FutureExecutor.defaultFactory

  def withDefaultFactory[R](h: (f: ScalettoExecutor.Factory) => (ev: SupportsCustomScheduler[f.ExecutionParam]) => R): R =
    h(libretto.scaletto.impl.futurebased.FutureExecutor.defaultFactory)(summon)
}
