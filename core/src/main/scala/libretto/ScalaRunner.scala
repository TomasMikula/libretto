package libretto

trait ScalaRunner[DSL <: ScalaDSL, F[_]] extends Runner[DSL, F] {
  val dsl: DSL

  import dsl._

  def runScala[A](prg: Done -⚬ Val[A]): F[A]

  override def run(prg: Done -⚬ Done): F[Unit] =
    runScala(dsl.andThen(prg, dsl.constVal(())))
}
