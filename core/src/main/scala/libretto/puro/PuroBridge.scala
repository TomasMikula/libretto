package libretto.puro

import libretto.exec.Bridge
import libretto.util.Async
import scala.concurrent.duration.FiniteDuration

trait PuroBridge extends Bridge {
  override type Dsl <: Puro

  import dsl.{|*|, |+|, |&|, =⚬, Done, One, Need, Ping, Pong}

  extension [I](using exn: Execution)(port: exn.InPort[I]) {
    def zipIn[J](j: exn.InPort[J]): exn.InPort[I |*| J]
  }

  extension (using exn: Execution)(port: exn.InPort[One]) {
    def dischargeOne(): Unit
  }

  extension (using exn: Execution)(port: exn.InPort[Done]) {
    def supplyDone(): Unit
  }

  extension [A, B](using exn: Execution)(port: exn.InPort[A |*| B]) {
    def unzipIn(): (exn.InPort[A], exn.InPort[B])
  }

  extension [A, B](using exn: Execution)(port: exn.InPort[A |+| B]) {
    def injectLeft(): exn.InPort[A]
    def injectRight(): exn.InPort[B]
  }

  extension [A, B](using exn: Execution)(port: exn.InPort[A |&| B]) {
    def awaitChoice(): Async[Either[Throwable, Either[exn.InPort[A], exn.InPort[B]]]]
  }

  extension [A](using exn: Execution)(port: exn.OutPort[A]) {
    def zip[B](b: exn.OutPort[B]): exn.OutPort[A |*| B]
  }

  extension (using exn: Execution)(port: exn.OutPort[One]) {
    def discardOne(): Unit
  }

  extension (using exn: Execution)(port: exn.OutPort[Done]) {
    def awaitDone(): Async[Either[Throwable, Unit]]
  }

  extension (using exn: Execution)(port: exn.OutPort[Ping]) {
    def awaitPing(): Async[Either[Throwable, Unit]]

    def awaitNoPing(
      duration: FiniteDuration,
    ): Async[Either[Either[Throwable, Unit], exn.OutPort[Ping]]]
  }

  extension (using exn: Execution)(port: exn.OutPort[Need]) {
    def supplyNeed(): Unit
  }

  extension (using exn: Execution)(port: exn.OutPort[Pong]) {
    def supplyPong(): Unit
  }

  extension [A, B](using exn: Execution)(port: exn.OutPort[A |*| B]) {
    def unzip(): (exn.OutPort[A], exn.OutPort[B])
  }

  extension [A, B](using exn: Execution)(port: exn.OutPort[A |+| B]) {
    def awaitEither(): Async[Either[Throwable, Either[exn.OutPort[A], exn.OutPort[B]]]]
  }

  extension [A, B](using exn: Execution)(port: exn.OutPort[A |&| B]) {
    def chooseLeft(): exn.OutPort[A]
    def chooseRight(): exn.OutPort[B]
  }

  extension [I, O](using exn: Execution)(port: exn.InPort[I =⚬ O]) {
    def simulateFunction(): (exn.OutPort[I], exn.InPort[O])
  }

  extension [I, O](using exn: Execution)(port: exn.OutPort[I =⚬ O]) {
    def useFunction(): (exn.InPort[I], exn.OutPort[O])
  }
}

object PuroBridge {
  type Of[DSL <: Puro] = PuroBridge { type Dsl = DSL }
}
