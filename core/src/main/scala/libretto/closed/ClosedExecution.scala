package libretto.closed

import libretto.CoreExecution

trait ClosedExecution[DSL <: ClosedDSL] extends CoreExecution[DSL] {
  import dsl.=⚬

  override val OutPort: ClosedOutPorts
  override val InPort:  ClosedInPorts

  trait ClosedOutPorts extends CoreOutPorts {
    def functionInputOutput[I, O](port: OutPort[I =⚬ O]): (InPort[I], OutPort[O])
  }

  trait ClosedInPorts extends CoreInPorts {
    def functionInputOutput[I, O](port: InPort[I =⚬ O]): (OutPort[I], InPort[O])
  }
}
