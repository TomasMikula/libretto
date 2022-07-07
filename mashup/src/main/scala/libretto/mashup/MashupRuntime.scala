package libretto.mashup

import libretto.util.Async

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

    def functionGetInOut[I, O](port: InPort[I --> O]): Async[(OutPort[I], InPort[O])]

    def unlimitedAwaitChoice[A](
      port: InPort[Unlimited[A]],
    ): Async[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]
  }

  trait OutPorts {
    def emptyResourceIgnore(port: OutPort[EmptyResource]): Unit

    def functionGetInOut[I, O](port: OutPort[I --> O]): Async[(InPort[I], OutPort[O])]

    def unlimitedIgnore[A](port: OutPort[Unlimited[A]]): Unit
    def unlimitedGetSingle[A](port: OutPort[Unlimited[A]]): Async[OutPort[A]]
    def unlimitedSplit[A](port: OutPort[Unlimited[A]]): Async[(OutPort[Unlimited[A]], OutPort[Unlimited[A]])]
  }
}
