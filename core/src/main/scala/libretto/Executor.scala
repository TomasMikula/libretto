package libretto

trait Executor[DSL <: CoreDSL, F[_]] {
  val dsl: DSL

  import dsl._

  type InPort[A]
  type OutPort[A]
  type Execution

  def execute[A, B](prg: A -⚬ B): (InPort[A], OutPort[B], Execution)

  def runAwait[A](fa: F[A]): A

  def cancel(execution: Execution): Unit

  def signalDone(port: InPort[Done]): F[Unit]
  def awaitDone(port: OutPort[Done]): F[Unit]
}
