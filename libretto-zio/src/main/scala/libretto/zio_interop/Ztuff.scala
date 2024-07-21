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

  private def feedTo(using
    bridge: ScalettoBridge.Of[StarterKit.dsl.type],
    exn: bridge.Execution,
  )(inPort: exn.InPort[A]): ZIO[Any, Nothing, Unit] =
    this match {
      case p: Pair[x, y] =>
        val (inPort1, inPort2) = exn.InPort.split[x, y](inPort)
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
      p.contramap(ValSource.fromChoice)

    exn.InPort
      .supplyChoice(unpack(inPort))
      .toZIO.absolve.orDie
      .flatMap {
        case Left(port) =>
          // no pull, ignore the input stream altogether
          ZIO.succeed(exn.InPort.supplyDone(port))
        case Right(port) =>
          type S = Option[exn.InPort[Done |+| (Val[X] |*| ValSource[X])]]
          stream
            .runFoldWhileZIO(Some(port): S)(_.isDefined) { (optPort, elem) =>
              val Some(port) = optPort: @unchecked
              val (pa, ps) = exn.InPort.split(exn.InPort.supplyRight(port))
              exn.InPort.supplyVal(pa, elem)
              exn.InPort.supplyChoice(unpack(ps)).toZIO.absolve.orDie.map {
                case Left(port) =>
                  exn.InPort.supplyDone(port)
                  None
                case Right(port) =>
                  Some(port)
              }
            }
            .map {
              case Some(port) => exn.InPort.supplyDone(exn.InPort.supplyLeft(port))
              case None       => ()
            }
      }
  }
}

object Ztuff {
  case class Pair[A, B](_1: Ztuff[A], _2: Ztuff[B]) extends Ztuff[A |*| B]
  case class ZioUStream[A](s: UStream[A]) extends Ztuff[ValSource[A]]
}
