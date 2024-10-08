package libretto.zio_interop

import libretto.scaletto.{ScalettoBridge, StarterKit}
import libretto.scaletto.StarterKit.{-⚬, |*|, |+|, |&|, Done, Val}
import libretto.stream.scaletto.DefaultStreams.ValSource
import zio.{Fiber, Scope, ZIO}
import zio.stream.UStream

/** ZIO stuff that can be mapped to Libretto type `A`. */
sealed trait Ztuff[A] {
  import Ztuff.*

  def |*|[B](that: Ztuff[B]): Ztuff[A |*| B] =
    Ztuff.Pair(this, that)

  def through[B](f: A -⚬ B): ZIO[Scope, Nothing, (Fiber.Runtime[Nothing, Unit], OutPort[B])] =
    val executorFactory = StarterKit.executorFactory
    ZIO
      .acquireRelease(ZIO.succeed(executorFactory.create()))(exec => ZIO.succeed(executorFactory.shutdown(exec)))
      .flatMap { executorResource =>
        val executor  = executorFactory.access(executorResource)
        val executing = executor.execute(f)
        import executing.bridge
        given execution: executing.execution.type = executing.execution
        this
          .feedTo(executing.inPort)
          .fork
          .map((_, OutPort(bridge, execution, executing.outPort)))
      }

  def through_[B](f: A -⚬ B): ZIO[Scope, Nothing, OutPort[B]] =
    through(f).map(_._2)

  private infix def feedTo(using
    bridge: ScalettoBridge.Of[StarterKit.dsl.type],
    exn: bridge.Execution,
  )(inPort: exn.InPort[A]): ZIO[Any, Nothing, Unit] =
    this match {
      case p: Pair[x, y] =>
        val (inPort1, inPort2) = (inPort: exn.InPort[x |*| y]).unzipIn()
        (p._1 feedTo inPort1) &> (p._2 feedTo inPort2)

      case ZioUStream(s) =>
        feedStream(s, inPort)
    }

  private def feedStream[X](using
    bridge: ScalettoBridge.Of[StarterKit.dsl.type],
    exn: bridge.Execution,
  )(
    stream: UStream[X],
    inPort: exn.InPort[ValSource[X]],
  ): ZIO[Any, Nothing, Unit] = {
    def unpack(p: exn.InPort[ValSource[X]]): exn.InPort[Done |&| (Done |+| (Val[X] |*| ValSource[X]))] =
      p.prepend(ValSource.fromChoice)

    unpack(inPort)
      .awaitChoice()
      .toZIO.absolve.orDie
      .flatMap {
        case Left(port) =>
          // no pull, ignore the input stream altogether
          ZIO.succeed(port.supplyDone())
        case Right(port) =>
          type S = Option[exn.InPort[Done |+| (Val[X] |*| ValSource[X])]]
          stream
            .runFoldWhileZIO(Some(port): S)(_.isDefined) { (optPort, elem) =>
              val Some(port) = optPort: @unchecked
              val (pa, ps) = port.injectRight().unzipIn()
              pa.supplyVal(elem)
              unpack(ps).awaitChoice().toZIO.absolve.orDie.map {
                case Left(port) =>
                  port.supplyDone()
                  None
                case Right(port) =>
                  Some(port)
              }
            }
            .map {
              case Some(port) => port.injectLeft().supplyDone()
              case None       => ()
            }
      }
  }
}

object Ztuff {
  case class Pair[A, B](_1: Ztuff[A], _2: Ztuff[B]) extends Ztuff[A |*| B]
  case class ZioUStream[A](s: UStream[A]) extends Ztuff[ValSource[A]]
}
