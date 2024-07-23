package libretto.scaletto.impl.futurebased

import libretto.exec.Executing
import libretto.exec.Executor.CancellationReason
import libretto.lambda.util.SourcePos
import libretto.scaletto.ScalettoBridge
import libretto.scaletto.impl.FreeScaletto
import libretto.util.{Async, Scheduler}
import scala.concurrent.ExecutionContext
import scala.concurrent.duration.FiniteDuration

object BridgeImpl extends ScalettoBridge {
  override type Dsl = FreeScaletto.type
  override val dsl: FreeScaletto.type = FreeScaletto
  import dsl.{-⚬, =⚬, |*|, |+|, |&|, Done, One, Need, Ping, Pong, Val}

  override opaque type Execution <: {
    type InPort[A]
    type OutPort[B]
  } = ExecutionImpl

  def execute[A, B](prg: A -⚬ B)(
    ec: ExecutionContext,
    scheduler: Scheduler,
    blockingEC: ExecutionContext,
  ): Executing[this.type, A, B] = {
    val execution = new ExecutionImpl(new ResourceRegistry, blockingEC)(using ec, scheduler)
    val (in, out) = execution.execute(prg)
    Executing(using this)(execution, in, out)
  }

  def cancelExecution(exn: Execution, pos: SourcePos): Async[Unit] =
    exn.cancel(pos)

  def watchForCancellation(exn: Execution): Async[CancellationReason] =
    exn.watchForCancellation()

  extension [I](using exn: Execution)(port: exn.InPort[I]) {
    override def prepend[H](f: H -⚬ I): exn.InPort[H] =
      exn.InPort.contramap(port)(f)

    override def zipIn[J](that: exn.InPort[J]): (exn.InPort[I |*| J]) =
      exn.InPort.pair(port, that)
  }

  extension (using exn: Execution)(port: exn.InPort[One]) {
    override def dischargeOne(): Unit =
      exn.InPort.discardOne(port)
  }

  extension (using exn: Execution)(port: exn.InPort[Done]) {
    override def supplyDone(): Unit =
      exn.InPort.supplyDone(port)
  }

  extension [A, B](using exn: Execution)(port: exn.InPort[A |*| B]) {
    override def unzipIn(): (exn.InPort[A], exn.InPort[B]) =
      exn.InPort.split(port)
  }

  extension [A, B](using exn: Execution)(port: exn.InPort[A |+| B]) {
    override def injectLeft(): exn.InPort[A]  = exn.InPort.supplyLeft(port)
    override def injectRight(): exn.InPort[B] = exn.InPort.supplyRight(port)
  }

  extension [A, B](using exn: Execution)(port: exn.InPort[A |&| B]) {
    def awaitChoice(): Async[Either[Throwable, Either[exn.InPort[A], exn.InPort[B]]]] =
      exn.InPort.supplyChoice(port)
  }

  extension [A](using exn: Execution)(port: exn.OutPort[A]) {
    override def append[B](f: A -⚬ B): exn.OutPort[B] =
      exn.OutPort.map(port)(f)

    override def zip[B](that: exn.OutPort[B]): exn.OutPort[A |*| B] =
      exn.OutPort.pair(port, that)
  }

  extension (using exn: Execution)(port: exn.OutPort[One]) {
    override def discardOne(): Unit =
      exn.OutPort.discardOne(port)
  }

  extension (using exn: Execution)(port: exn.OutPort[Done]) {
    override def awaitDone(): Async[Either[Throwable, Unit]] =
      exn.OutPort.awaitDone(port)
  }

  extension (using exn: Execution)(port: exn.OutPort[Ping]) {
    override def awaitPing(): Async[Either[Throwable, Unit]] =
      exn.OutPort.awaitPing(port)

    override def awaitNoPing(
      duration: FiniteDuration,
    ): Async[Either[Either[Throwable, Unit], exn.OutPort[Ping]]] =
      exn.OutPort.awaitNoPing(port, duration)
  }

  extension (using exn: Execution)(port: exn.OutPort[Need]) {
    override def supplyNeed(): Unit =
      exn.OutPort.supplyNeed(port)
  }

  extension (using exn: Execution)(port: exn.OutPort[Pong]) {
    override def supplyPong(): Unit =
      exn.OutPort.supplyPong(port)
  }

  extension [A, B](using exn: Execution)(port: exn.OutPort[A |*| B]) {
    override def unzip(): (exn.OutPort[A], exn.OutPort[B]) =
      exn.OutPort.split(port)
  }

  extension [A, B](using exn: Execution)(port: exn.OutPort[A |+| B]) {
    override def awaitEither(): Async[Either[Throwable, Either[exn.OutPort[A], exn.OutPort[B]]]] =
      exn.OutPort.awaitEither(port)
  }

  extension [A, B](using exn: Execution)(port: exn.OutPort[A |&| B]) {
    override def chooseLeft(): exn.OutPort[A]  = exn.OutPort.chooseLeft(port)
    override def chooseRight(): exn.OutPort[B] = exn.OutPort.chooseRight(port)
  }

  extension [I, O](using exn: Execution)(port: exn.InPort[I =⚬ O]) {
    override def simulateFunction(): (exn.OutPort[I], exn.InPort[O]) =
      exn.InPort.functionInputOutput(port)
  }

  extension [I, O](using exn: Execution)(port: exn.OutPort[I =⚬ O]) {
    override def useFunction(): (exn.InPort[I], exn.OutPort[O]) =
      exn.OutPort.functionInputOutput(port)
  }

  extension [A](using exn: Execution)(port: exn.InPort[Val[A]]) {
    override def supplyVal(value: A): Unit =
      exn.InPort.supplyVal(port, value)
  }

  extension [A](using exn: Execution)(port: exn.OutPort[Val[A]]) {
    override def awaitVal(): Async[Either[Throwable, A]] =
      exn.OutPort.awaitVal(port)
  }
}
