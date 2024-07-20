package libretto.exec

final class Executing[BRIDGE <: Bridge, A, B](using val bridge: BRIDGE)(
  val execution: bridge.Execution,
  val inPort: execution.InPort[A],
  val outPort: execution.OutPort[B],
)
