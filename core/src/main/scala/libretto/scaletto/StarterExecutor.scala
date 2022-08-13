package libretto.scaletto

type StarterExecutor = ScalettoExecutor.Of[StarterKit.dsl.type, StarterKit.bridge.type]

object StarterExecutor {
  val defaultFactory: ScalettoExecutor.Factory.Of[StarterKit.dsl.type, StarterKit.bridge.type] =
    ScalettoExecutor.defaultFactory0
}