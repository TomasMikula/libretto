package libretto

trait CoreBridge[F[_]] {
  type Dsl <: CoreDSL

  val dsl: Dsl

  import dsl._

  type OutPort[A]

  def awaitDone(port: OutPort[Done]): F[Either[Throwable, Unit]]

  def awaitEither[A, B](port: OutPort[A |+| B]): F[Either[Throwable, Either[OutPort[A], OutPort[B]]]]
}

object CoreBridge {
  type Of[DSL <: CoreDSL, F[_]] = CoreBridge[F] { type Dsl = DSL }
}

trait ScalaBridge[F[_]] extends CoreBridge[F] {
  override type Dsl <: ScalaDSL

  import dsl.Val

  def awaitVal[A](port: OutPort[Val[A]]): F[Either[Throwable, A]]
}

trait Executor[F[_]] extends CoreBridge[F] {
  import dsl._

  type Execution

  def execute[B](prg: Done -⚬ B): (OutPort[B], Execution)

  def runAwait[A](fa: F[A]): A

  def cancel(execution: Execution): F[Unit]
}

object Executor {
  type Of[DSL <: CoreDSL, F[_]] = Executor[F] { type Dsl = DSL }
}

trait ScalaExecutor[F[_]] extends Executor[F] with ScalaBridge[F]

object ScalaExecutor {
  type Of[DSL <: ScalaDSL, F[_]] = ScalaExecutor[F] { type Dsl = DSL }
}
