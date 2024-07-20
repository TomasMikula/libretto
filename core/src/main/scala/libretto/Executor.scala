package libretto

import libretto.lambda.util.SourcePos
import libretto.util.Async

final class Executing[BRIDGE <: CoreBridge & Singleton, A, B](using val bridge: BRIDGE)(
  val execution: bridge.Execution,
  val inPort: execution.InPort[A],
  val outPort: execution.OutPort[B],
)

trait Executor { self =>
  import Executor.CancellationReason

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

  type ExecutionParams[A] = libretto.ExecutionParams[ExecutionParam, A]

  def execute[A, B, P](
    prg: A -⚬ B,
    params: ExecutionParams[P],
  ): (Executing[bridge.type, A, B], P)

  final def execute[A, B](prg: A -⚬ B): Executing[bridge.type, A, B] =
    execute(prg, ExecutionParams.unit)._1

  def cancel(using pos: SourcePos)(execution: Execution): Async[Unit]

  /** Watch for abrupt cancellation of the given [[Execution]].
    * If the execution completes normally, the returned [[Async]] may never complete.
    */
  def watchForCancellation(execution: Execution): Async[CancellationReason]

  def narrow: Executor.Of[dsl.type, bridge.type] =
    new Executor {
      override type Dsl = self.dsl.type
      override type Bridge = self.bridge.type

      export self.{dsl, bridge, ExecutionParam, execute, cancel, watchForCancellation}
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

    def name: String
    def create(): ExecutorResource
    def access(r: ExecutorResource): Executor.Of[dsl.type, bridge.type]
    def shutdown(r: ExecutorResource): Unit
  }

  object Factory {
    type Of[DSL <: CoreDSL, BRIDGE <: CoreBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }

  enum CancellationReason {
    case User(position: SourcePos)
    case Bug(message: String, cause: Option[Throwable])
  }
}
