package libretto.closed

trait ClosedExecution[DSL <: ClosedDSL] {
  val dsl: DSL
  import dsl.=⚬

  type InPort[A]
  type OutPort[B]

  val OutPort: ClosedOutPorts
  val InPort:  ClosedInPorts

  trait ClosedOutPorts {
    def functionInputOutput[I, O](port: OutPort[I =⚬ O]): (InPort[I], OutPort[O])
  }

  trait ClosedInPorts {
    def functionInputOutput[I, O](port: InPort[I =⚬ O]): (OutPort[I], InPort[O])
  }
}
