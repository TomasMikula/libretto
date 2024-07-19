package libretto

trait ClosedExecution[DSL <: ClosedDSL] extends CoreExecution[DSL] {
  import dsl.=⚬

  override val OutPort: ClosedOutPorts
  override val InPort:  ClosedInPorts

  trait ClosedOutPorts extends OutPorts {
    def functionInputOutput[I, O](port: OutPort[I =⚬ O]): (InPort[I], OutPort[O])
  }

  trait ClosedInPorts extends InPorts {
    def functionInputOutput[I, O](port: InPort[I =⚬ O]): (OutPort[I], InPort[O])
  }
}
