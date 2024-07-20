package libretto

import libretto.exec.Executor

trait CoreExecutor extends Executor {
  override val dsl: CoreDSL
  override val bridge: CoreBridge.Of[dsl.type]
}
