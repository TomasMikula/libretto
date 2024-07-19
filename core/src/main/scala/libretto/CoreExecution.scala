package libretto

import libretto.util.Async
import scala.annotation.targetName
import scala.concurrent.duration.FiniteDuration

trait CoreExecution[DSL <: CoreDSL] {
  val dsl: DSL
  import dsl.*

  type OutPort[A]
  val OutPort: OutPorts

  type InPort[A]
  val InPort: InPorts

  trait OutPorts {
    def map[A, B](port: OutPort[A])(f: A -⚬ B): OutPort[B]

    def pair[A, B](a: OutPort[A], b: OutPort[B]): OutPort[A |*| B]

    def split[A, B](port: OutPort[A |*| B]): (OutPort[A], OutPort[B])

    def constant[A](obj: One -⚬ A): OutPort[A]

    def discardOne(port: OutPort[One]): Unit

    def awaitDone(port: OutPort[Done]): Async[Either[Throwable, Unit]]

    def awaitPing(port: OutPort[Ping]): Async[Either[Throwable, Unit]]

    def awaitNoPing(
      port: OutPort[Ping],
      duration: FiniteDuration,
    ): Async[Either[Either[Throwable, Unit], OutPort[Ping]]]

    def supplyNeed(port: OutPort[Need]): Unit

    def supplyPong(port: OutPort[Pong]): Unit

    @deprecated("Use supplyPong")
    def sendPong(port: OutPort[Pong]): Unit =
      supplyPong(port)

    def awaitEither[A, B](port: OutPort[A |+| B]): Async[Either[Throwable, Either[OutPort[A], OutPort[B]]]]

    def chooseLeft[A, B](port: OutPort[A |&| B]): OutPort[A]

    def chooseRight[A, B](port: OutPort[A |&| B]): OutPort[B]
  }

  extension [A](port: OutPort[A]) {
    @targetName("outPortMap")
    def map[B](f: A -⚬ B): OutPort[B] =
      OutPort.map(port)(f)

    @targetName("outPortDiscard")
    def discard(using ev: A =:= One): Unit =
      OutPort.discardOne(ev.substituteCo(port))
  }

  trait InPorts {
    def contramap[A, B](port: InPort[B])(f: A -⚬ B): InPort[A]

    def pair[A, B](a: InPort[A], b: InPort[B]): InPort[A |*| B]

    def split[A, B](port: InPort[A |*| B]): (InPort[A], InPort[B])

    def constant[A](f: A -⚬ One): InPort[A]

    def discardOne(port: InPort[One]): Unit

    def supplyDone(port: InPort[Done]): Unit

    def supplyPing(port: InPort[Ping]): Unit

    def supplyLeft[A, B](port: InPort[A |+| B]): InPort[A]

    def supplyRight[A, B](port: InPort[A |+| B]): InPort[B]

    def supplyChoice[A, B](port: InPort[A |&| B]): Async[Either[Throwable, Either[InPort[A], InPort[B]]]]
  }
}
