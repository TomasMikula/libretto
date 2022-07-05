package libretto

import libretto.util.Monad
import libretto.util.Monad.syntax._

trait ScalaRunner[DSL <: ScalaDSL, F[_]] extends Runner[DSL, F] {
  val dsl: DSL

  import dsl._

  def runScala[A](prg: Done -⚬ Val[A]): F[A]

  override def run(prg: Done -⚬ Done): F[Unit] =
    runScala(dsl.andThen(prg, dsl.constVal(())))
}

object ScalaRunner {
  def fromExecutor[DSL <: ScalaDSL, F[_]](
    executor: ScalaExecutor.Of[DSL, F],
    raiseError: [a] => Throwable => F[a],
  )(using
    F: Monad[F],
  ): ScalaRunner[DSL, F] =
    new ScalaRunner[DSL, F] {
      override val dsl: executor.dsl.type = executor.dsl

      import dsl._

      override def runScala[A](prg: Done -⚬ Val[A]): F[A] =
        import executor.{InPort, OutPort}

        val (inPort, outPort, execution) =
          executor.execute(prg)

        for {
          _   <- InPort.supplyDone(inPort)
          res <- OutPort.awaitVal(outPort)
          _   <- executor.cancel(execution)
          a   <- res match {
                   case Right(a) => F.pure(a)
                   case Left(e)  => raiseError(e)
                 }
        } yield a
    }
}
