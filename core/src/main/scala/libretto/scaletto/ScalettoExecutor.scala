package libretto.scaletto

import libretto.exec.{Executor, SupportsCustomScheduler}

object ScalettoExecutor {
  val defaultFactory: Executor.Factory.Of[Scaletto, ScalettoBridge] =
    libretto.scaletto.impl.futurebased.FutureExecutor.defaultFactory

  def withDefaultFactory[R](h: (f: Executor.Factory.Of[Scaletto, ScalettoBridge]) => (ev: SupportsCustomScheduler[f.ExecutionParam]) => R): R =
    h(libretto.scaletto.impl.futurebased.FutureExecutor.defaultFactory)(summon)
}
