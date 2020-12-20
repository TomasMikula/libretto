package libretto

trait ScalaRunner[DSL <: ScalaDSL, F[_]] extends Runner[DSL, F] {
  val dsl: DSL
  
  import dsl._
  
  def runScala[A](prg: One -⚬ Val[A]): F[A]

  override def run(prg: One -⚬ Done): F[Unit] =
    runScala(dsl.andThen(prg, dsl.constVal(())))
}
