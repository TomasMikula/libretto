package libretto.mashup

import libretto.util.Async
import scala.util.Try

trait MashupRuntime[DSL <: MashupDsl] {
  val dsl: DSL

  import dsl.{-->, **, ##, EmptyResource, Float64, Fun, Record, Text, Unlimited, of}

  type Value[A]
  val Value: Values

  type Execution <: MashupExecution

  class Executing[A, B](
    val execution: Execution,
    val inPort: execution.InPort[A],
    val outPort: execution.OutPort[B],
  )

  def run[A, B](f: Fun[A, B]): Executing[A, B]

  trait Values {
    def unit: Value[EmptyResource]

    def pair[A, B](a: Value[A], b: Value[B]): Value[A ** B]

    def text(value: String): Value[Text]
    def textGet(value: Value[Text]): String

    def float64(value: Double): Value[Float64]
    def float64Get(value: Value[Float64]): Double

    def emptyRecord: Value[Record[EmptyResource]]

    def record[K <: String & Singleton, T](key: K, value: Value[T]): Value[Record[K of T]]

    def extendRecord[A, Name <: String, T](
      init: Value[Record[A]],
      name: Name,
      last: Value[T],
    ): Value[Record[A ## (Name of T)]]
  }

  extension [A](a: Value[A]) {
    def **[B](b: Value[B]): Value[A ** B] =
      Value.pair(a, b)
  }

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

      def textSupply(port: InPort[Text], value: String): Unit

      def float64Supply(port: InPort[Float64], value: Double): Unit

      def valueSupply[A](port: InPort[A], value: Value[A]): Unit
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

      def textGet(port: OutPort[Text]): Async[Try[String]]

      def float64Get(port: OutPort[Float64]): Async[Try[Double]]

      def recordIgnoreEmpty(port: OutPort[Record[EmptyResource]]): Unit
      def recordGetSingle[N <: String, T](port: OutPort[Record[N of T]]): OutPort[T]
      def recordUnsnoc[A, N <: String, T](port: OutPort[Record[A ## (N of T)]]): (OutPort[Record[A]], OutPort[T])
    }
  }
}
