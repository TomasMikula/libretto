package libretto

import libretto.util.Async

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

    def name: String
    def create(): ExecutorResource
    def access(r: ExecutorResource): Executor.Of[dsl.type, bridge.type]
    def shutdown(r: ExecutorResource): Unit
  }

  object Factory {
    type Of[DSL <: CoreDSL, BRIDGE <: CoreBridge.Of[DSL]] =
      Factory { type Dsl = DSL; type Bridge = BRIDGE }
  }
}
