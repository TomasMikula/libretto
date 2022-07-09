package libretto

import libretto.util.Async
import scala.concurrent.Future

trait ScalaRunner[DSL <: ScalaDSL] extends Runner[DSL] {
  val dsl: DSL

  import dsl._

  def runScala[A](prg: Done -⚬ Val[A]): Future[A]

  override def run(prg: Done -⚬ Done): Future[Unit] =
    runScala(dsl.andThen(prg, dsl.constVal(())))
}

object ScalaRunner {
  def fromExecutor[DSL <: ScalaDSL](
    executor: ScalaExecutor.Of[DSL],
  ): ScalaRunner[DSL] =
    new ScalaRunner[DSL] {
      override val dsl: executor.dsl.type = executor.dsl

      import dsl._

      override def runScala[A](prg: Done -⚬ Val[A]): Future[A] =
        val executing = executor.execute(prg)
        import executing.{execution, inPort, outPort}
        import execution.{InPort, OutPort}

        val () = InPort.supplyDone(inPort)
        Async.toFuture {
          for {
            res <- OutPort.awaitVal(outPort)
            _   <- executor.cancel(execution)
          } yield
            res match {
              case Right(a) => Future.successful(a)
              case Left(e)  => Future.failed(e)
            }
        }.flatten
    }
}
