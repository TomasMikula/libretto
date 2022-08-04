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

trait Executor {
  type Dsl <: CoreDSL
  val dsl: Dsl

  type Bridge <: CoreBridge.Of[dsl.type]
  val bridge: Bridge

  import dsl.-⚬
  import bridge.Execution

  final class Executing[A, B](
    val execution: Execution,
    val inPort: execution.InPort[A],
    val outPort: execution.OutPort[B],
  )

  def execute[A, B](prg: A -⚬ B): Executing[A, B]

  def cancel(execution: Execution): Async[Unit]
}

object Executor {
  type Of[DSL <: CoreDSL, BRIDGE <: CoreBridge.Of[DSL]] =
    Executor { type Dsl = DSL; type Bridge = BRIDGE }
}

trait ScalaExecutor extends Executor {
  override type Dsl <: ScalaDSL
  override type Bridge <: ScalaBridge.Of[dsl.type]
}

object ScalaExecutor {
  type OfDsl[DSL <: ScalaDSL] = ScalaExecutor { type Dsl = DSL }

  type Of[DSL <: ScalaDSL, BRIDGE <: ScalaBridge.Of[DSL]] =
    ScalaExecutor { type Dsl = DSL; type Bridge = BRIDGE }
}
