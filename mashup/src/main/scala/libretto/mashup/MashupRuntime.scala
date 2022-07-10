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
      def contramap[A, B](port: InPort[B])(f: Fun[A, B]): InPort[A]

      def emptyResourceIgnore(port: InPort[EmptyResource]): Unit

      def functionInputOutput[I, O](port: InPort[I --> O]): (OutPort[I], InPort[O])

      def unlimitedAwaitChoice[A](
        port: InPort[Unlimited[A]],
      ): Async[Try[Option[Either[InPort[A], (InPort[Unlimited[A]], InPort[Unlimited[A]])]]]]
    }

    trait OutPorts {
      def map[A, B](port: OutPort[A])(f: Fun[A, B]): OutPort[B]

      def emptyResourceIgnore(port: OutPort[EmptyResource]): Unit

      def functionInputOutput[I, O](port: OutPort[I --> O]): (InPort[I], OutPort[O])

      def unlimitedIgnore[A](port: OutPort[Unlimited[A]]): Unit
      def unlimitedGetSingle[A](port: OutPort[Unlimited[A]]): OutPort[A]
      def unlimitedSplit[A](port: OutPort[Unlimited[A]]): (OutPort[Unlimited[A]], OutPort[Unlimited[A]])

      def unlimitedUncons[A](port: OutPort[Unlimited[A]]): (OutPort[A], OutPort[Unlimited[A]]) =
        val (p1, p2) = unlimitedSplit(port)
        (unlimitedGetSingle(p1), p2)
    }
  }
}
