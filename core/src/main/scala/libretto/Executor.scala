package libretto

trait CoreBridge[F[_]] {
  type Dsl <: CoreDSL

  val dsl: Dsl

  import dsl._

  type OutPort[A]
  val OutPort: OutPorts

  trait OutPorts {
    def split[A, B](port: OutPort[A |*| B]): F[(OutPort[A], OutPort[B])]

    def awaitDone(port: OutPort[Done]): F[Either[Throwable, Unit]]

    def awaitEither[A, B](port: OutPort[A |+| B]): F[Either[Throwable, Either[OutPort[A], OutPort[B]]]]
  }
}

object CoreBridge {
  type Of[DSL <: CoreDSL, F[_]] = CoreBridge[F] { type Dsl = DSL }
}

trait ScalaBridge[F[_]] extends CoreBridge[F] {
  override type Dsl <: ScalaDSL

  import dsl.Val

  override val OutPort: ScalaOutPorts

  trait ScalaOutPorts extends OutPorts {
    def awaitVal[A](port: OutPort[Val[A]]): F[Either[Throwable, A]]
  }
}

object ScalaBridge {
  type Of[DSL <: ScalaDSL, F[_]] = ScalaBridge[F] { type Dsl = DSL }
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
