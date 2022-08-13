package libretto

import libretto.util.Async

/** Defines interface to interact with a running Libretto program. */
trait CoreBridge {
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
      def map[A, B](port: OutPort[A])(f: A -⚬ B): OutPort[B]

      def split[A, B](port: OutPort[A |*| B]): (OutPort[A], OutPort[B])

      def discardOne(port: OutPort[One]): Unit

      def awaitDone(port: OutPort[Done]): Async[Either[Throwable, Unit]]

      def awaitEither[A, B](port: OutPort[A |+| B]): Async[Either[Throwable, Either[OutPort[A], OutPort[B]]]]

      def chooseLeft[A, B](port: OutPort[A |&| B]): OutPort[A]

      def chooseRight[A, B](port: OutPort[A |&| B]): OutPort[B]
    }

    trait InPorts {
      def contramap[A, B](port: InPort[B])(f: A -⚬ B): InPort[A]

      def split[A, B](port: InPort[A |*| B]): (InPort[A], InPort[B])

      def discardOne(port: InPort[One]): Unit

      def supplyDone(port: InPort[Done]): Unit

      def supplyLeft[A, B](port: InPort[A |+| B]): InPort[A]

      def supplyRight[A, B](port: InPort[A |+| B]): InPort[B]

      def supplyChoice[A, B](port: InPort[A |&| B]): Async[Either[Throwable, Either[InPort[A], InPort[B]]]]
    }
  }
}

object CoreBridge {
  type Of[DSL <: CoreDSL] = CoreBridge { type Dsl = DSL }
}

trait ClosedBridge extends CoreBridge {
  override type Dsl <: ClosedDSL

  import dsl.=⚬

  override type Execution <: ClosedExecution

  trait ClosedExecution extends CoreExecution {
    override val OutPort: ClosedOutPorts
    override val InPort:  ClosedInPorts

    trait ClosedOutPorts extends OutPorts {
      def functionInputOutput[I, O](port: OutPort[I =⚬ O]): (InPort[I], OutPort[O])
    }

    trait ClosedInPorts extends InPorts {
      def functionInputOutput[I, O](port: InPort[I =⚬ O]): (OutPort[I], InPort[O])
    }
  }
}

object ClosedBridge {
  type Of[DSL <: ClosedDSL] = ClosedBridge { type Dsl = DSL }
}

final class Executing[BRIDGE <: CoreBridge & Singleton, A, B](using val bridge: BRIDGE)(
  val execution: bridge.Execution,
  val inPort: execution.InPort[A],
  val outPort: execution.OutPort[B],
)

trait Executor { self =>
  type Dsl <: CoreDSL
  val dsl: Dsl

  type Bridge <: CoreBridge.Of[dsl.type]
  val bridge: Bridge

  import dsl.-⚬
  import bridge.Execution

  /** Type of parameters used to tweak execution.
    *
    * @tparam A returned to the caller when execution starts
    */
  type ExecutionParam[A]
  val  ExecutionParam: ExecutionParams[ExecutionParam]

  def execute[A, B, P](
    prg: A -⚬ B,
    params: ExecutionParam[P],
  ): (Executing[bridge.type, A, B], P)

  final def execute[A, B](prg: A -⚬ B): Executing[bridge.type, A, B] =
    execute(prg, ExecutionParam.unit)._1

  def cancel(execution: Execution): Async[Unit]

  def narrow: Executor.Of[dsl.type, bridge.type] =
    new Executor {
      override type Dsl = self.dsl.type
      override type Bridge = self.bridge.type

      export self.{dsl, bridge, ExecutionParam, execute, cancel}
    }
}

object Executor {
  type Of[DSL <: CoreDSL, BRIDGE <: CoreBridge.Of[DSL]] =
    Executor { type Dsl = DSL; type Bridge = BRIDGE }

  trait Factory {
    type Dsl <: CoreDSL
    val dsl: Dsl

    type Bridge <: CoreBridge.Of[dsl.type]
    val bridge: Bridge

    type ExecutorResource

    def create(): ExecutorResource
    def access(r: ExecutorResource): Executor.Of[dsl.type, bridge.type]
    def shutdown(r: ExecutorResource): Unit
  }

  object Factory {
    type Of[DSL <: CoreDSL, BRIDGE <: CoreBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }
}
