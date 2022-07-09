package libretto.mashup

import libretto.util.Async
import scala.util.Try

trait MashupRuntime[DSL <: MashupDsl] {
  val dsl: DSL

  import dsl.{-->, EmptyResource, Unlimited}

  type InPort[A]
  val InPort: InPorts

  type OutPort[A]
  val OutPort: OutPorts

  type Execution

  import dsl.Fun

  def run[A, B](f: Fun[A, B]): (InPort[A], OutPort[B], Execution)

  trait InPorts {
    def emptyResourceIgnore(port: InPort[EmptyResource]): Unit

    def functionInputOutput[I, O](port: InPort[I --> O]): Async[(OutPort[I], InPort[O])]

    def unlimitedAwaitChoice[A](
      port: InPort[Unlimited[A]],
    )(
      exn: Execution, // TODO: execution should be built into InPort
    ): Async[Try[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]]
  }

  trait OutPorts {
    def emptyResourceIgnore(port: OutPort[EmptyResource]): Unit

    def functionInputOutput[I, O](port: OutPort[I --> O]): Async[(InPort[I], OutPort[O])]

    def unlimitedIgnore[A](port: OutPort[Unlimited[A]])(exn: Execution): Unit
    def unlimitedGetSingle[A](port: OutPort[Unlimited[A]])(exn: Execution): Async[OutPort[A]]
    def unlimitedSplit[A](port: OutPort[Unlimited[A]])(exn: Execution): Async[(OutPort[Unlimited[A]], OutPort[Unlimited[A]])]
  }
}
