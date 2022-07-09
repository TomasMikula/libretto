package libretto.mashup

import libretto.util.Async
import scala.util.Try

trait MashupRuntime[DSL <: MashupDsl] {
  val dsl: DSL

  import dsl.{-->, EmptyResource, Fun, Unlimited}

  type Execution <: MashupExecution

  class Executing[A, B](
    val execution: Execution,
    val inPort: execution.InPort[A],
    val outPort: execution.OutPort[B],
  )

  def run[A, B](f: Fun[A, B]): Executing[A, B]

  trait MashupExecution {
    type InPort[A]
    val InPort: InPorts

    type OutPort[A]
    val OutPort: OutPorts

    trait InPorts {
      def emptyResourceIgnore(port: InPort[EmptyResource]): Unit

      def functionInputOutput[I, O](port: InPort[I --> O]): Async[(OutPort[I], InPort[O])]

      def unlimitedAwaitChoice[A](
        port: InPort[Unlimited[A]],
      ): Async[Try[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]]
    }

    trait OutPorts {
      def emptyResourceIgnore(port: OutPort[EmptyResource]): Unit

      def functionInputOutput[I, O](port: OutPort[I --> O]): Async[(InPort[I], OutPort[O])]

      def unlimitedIgnore[A](port: OutPort[Unlimited[A]]): Unit
      def unlimitedGetSingle[A](port: OutPort[Unlimited[A]]): Async[OutPort[A]]
      def unlimitedSplit[A](port: OutPort[Unlimited[A]]): Async[(OutPort[Unlimited[A]], OutPort[Unlimited[A]])]
    }
  }
}
