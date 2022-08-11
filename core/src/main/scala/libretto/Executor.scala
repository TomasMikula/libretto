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

trait ScalaBridge extends ClosedBridge {
  override type Dsl <: ScalaDSL

  import dsl.Val

  override type Execution <: ScalaExecution

  trait ScalaExecution extends ClosedExecution {
    override val OutPort: ScalaOutPorts
    override val InPort:  ScalaInPorts

    trait ScalaOutPorts extends ClosedOutPorts {
      def awaitVal[A](port: OutPort[Val[A]]): Async[Either[Throwable, A]]
    }

    trait ScalaInPorts extends ClosedInPorts {
      def supplyVal[A](port: InPort[Val[A]], value: A): Unit
    }
  }
}

object ScalaBridge {
  type Of[DSL <: ScalaDSL] = ScalaBridge { type Dsl = DSL }
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

    type Exec

    def create(): Exec
    def access(e: Exec): Executor.Of[dsl.type, bridge.type]
    def shutdown(e: Exec): Unit
  }

  object Factory {
    type Of[DSL <: CoreDSL, BRIDGE <: CoreBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }
}

trait ScalaExecutor extends Executor { self =>
  override type Dsl <: ScalaDSL
  override type Bridge <: ScalaBridge.Of[dsl.type]

  override val ExecutionParam: ExecutionParams.WithScheduler[ExecutionParam]

  override def narrow: ScalaExecutor.Of[dsl.type, bridge.type] =
    new ScalaExecutor {
      override type Dsl = self.dsl.type
      override type Bridge = self.bridge.type

      export self.{dsl, bridge, ExecutionParam, execute, cancel}
    }
}

object ScalaExecutor {
  type OfDsl[DSL <: ScalaDSL] = ScalaExecutor { type Dsl = DSL }

  type Of[DSL <: ScalaDSL, BRIDGE <: ScalaBridge.Of[DSL]] =
    ScalaExecutor { type Dsl = DSL; type Bridge = BRIDGE }

  trait Factory extends Executor.Factory {
    override type Dsl <: ScalaDSL
    override type Bridge <: ScalaBridge.Of[dsl.type]

    override def access(e: Exec): ScalaExecutor.Of[dsl.type, bridge.type]
  }

  object Factory {
    type Of[DSL <: ScalaDSL, BRIDGE <: ScalaBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }

  private[libretto] val defaultFactory0: ScalaExecutor.Factory.Of[StarterKit.dsl.type, StarterKit.bridge.type] =
    new ScalaExecutor.Factory {
      import java.util.concurrent.{Executors, ExecutorService, ScheduledExecutorService}

      override type Dsl = StarterKit.dsl.type
      override type Bridge = StarterKit.bridge.type

      override val dsl = StarterKit.dsl
      override val bridge = StarterKit.bridge

      override type Exec = (ScheduledExecutorService, ExecutorService, ScalaExecutor.Of[dsl.type, bridge.type])

      override def access(e: Exec): ScalaExecutor.Of[dsl.type, bridge.type] =
        e._3

      override def create(): Exec = {
        val scheduler = Executors.newScheduledThreadPool(Runtime.getRuntime().availableProcessors())
        val blockingExecutor = Executors.newCachedThreadPool()
        val executor = StarterKit.executor(blockingExecutor)(scheduler)
        (scheduler, blockingExecutor, executor)
      }

      override def shutdown(exec: Exec): Unit = {
        exec._2.shutdownNow()
        exec._1.shutdownNow()
      }
    }

  val defaultFactory: ScalaExecutor.Factory =
    defaultFactory0
}

type StarterExecutor = ScalaExecutor.Of[StarterKit.dsl.type, StarterKit.bridge.type]

object StarterExecutor {
  val defaultFactory: ScalaExecutor.Factory.Of[StarterKit.dsl.type, StarterKit.bridge.type] =
    ScalaExecutor.defaultFactory0
}
