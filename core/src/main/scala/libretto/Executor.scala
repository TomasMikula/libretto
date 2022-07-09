package libretto

/** Defines interface to interact with a running Libretto program. */
trait CoreBridge[F[_]] {
  type Dsl <: CoreDSL

  val dsl: Dsl

  import dsl._

  /** Handle to a running Libretto program. */
  type Execution <: CoreExecution

  trait CoreExecution {
    type OutPort[A]
    val OutPort: OutPorts

    type InPort[A]
    val InPort: InPorts

    trait OutPorts {
      def map[A, B](port: OutPort[A])(f: A -⚬ B): F[OutPort[B]]

      def split[A, B](port: OutPort[A |*| B]): F[(OutPort[A], OutPort[B])]

      def discardOne(port: OutPort[One]): F[Unit]

      def awaitDone(port: OutPort[Done]): F[Either[Throwable, Unit]]

      def awaitEither[A, B](port: OutPort[A |+| B]): F[Either[Throwable, Either[OutPort[A], OutPort[B]]]]

      def chooseLeft[A, B](port: OutPort[A |&| B]): F[OutPort[A]]

      def chooseRight[A, B](port: OutPort[A |&| B]): F[OutPort[B]]
    }

    trait InPorts {
      def contramap[A, B](port: InPort[B])(f: A -⚬ B): F[InPort[A]]

      def split[A, B](port: InPort[A |*| B]): F[(InPort[A], InPort[B])]

      def discardOne(port: InPort[One]): F[Unit]

      def supplyDone(port: InPort[Done]): F[Unit]

      def supplyLeft[A, B](port: InPort[A |+| B]): F[InPort[A]]

      def supplyRight[A, B](port: InPort[A |+| B]): F[InPort[B]]

      def supplyChoice[A, B](port: InPort[A |&| B]): F[Either[Throwable, Either[InPort[A], InPort[B]]]]
    }
  }
}

object CoreBridge {
  type Of[DSL <: CoreDSL, F[_]] = CoreBridge[F] { type Dsl = DSL }
}

trait ClosedBridge[F[_]] extends CoreBridge[F] {
  override type Dsl <: ClosedDSL

  import dsl.=⚬

  override type Execution <: ClosedExecution

  trait ClosedExecution extends CoreExecution {
    override val OutPort: ClosedOutPorts
    override val InPort:  ClosedInPorts

    trait ClosedOutPorts extends OutPorts {
      def functionInputOutput[I, O](port: OutPort[I =⚬ O]): F[(InPort[I], OutPort[O])]
    }

    trait ClosedInPorts extends InPorts {
      def functionInputOutput[I, O](port: InPort[I =⚬ O]): F[(OutPort[I], InPort[O])]
    }
  }
}

object ClosedBridge {
  type Of[DSL <: ClosedDSL, F[_]] = ClosedBridge[F] { type Dsl = DSL }
}

trait ScalaBridge[F[_]] extends ClosedBridge[F] {
  override type Dsl <: ScalaDSL

  import dsl.Val

  override type Execution <: ScalaExecution

  trait ScalaExecution extends ClosedExecution {
    override val OutPort: ScalaOutPorts
    override val InPort:  ScalaInPorts

    trait ScalaOutPorts extends ClosedOutPorts {
      def awaitVal[A](port: OutPort[Val[A]]): F[Either[Throwable, A]]
    }

    trait ScalaInPorts extends ClosedInPorts {
      def supplyVal[A](port: InPort[Val[A]], value: A): F[Unit]
    }
  }
}

object ScalaBridge {
  type Of[DSL <: ScalaDSL, F[_]] = ScalaBridge[F] { type Dsl = DSL }
}

trait Executor[F[_]] extends CoreBridge[F] {
  import dsl._

  final class Executing[A, B](
    val execution: Execution,
    val inPort: execution.InPort[A],
    val outPort: execution.OutPort[B],
  )

  def execute[A, B](prg: A -⚬ B): Executing[A, B]

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
