package libretto.exec

import libretto.lambda.util.SourcePos
import libretto.util.Async

trait Executor { self =>
  import Executor.CancellationReason

  val dsl: { type -⚬[A, B] }
  val bridge: Bridge.Of[dsl.type]

  import dsl.-⚬
  import bridge.Execution

  /** Type of parameters used to tweak execution.
    *
    * @tparam A returned to the caller when execution starts
    */
  type ExecutionParam[A]

  type ExecutionParams[A] = libretto.exec.ExecutionParams[ExecutionParam, A]

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
}

object Executor {
  type Of[DSL <: { type -⚬[A, B] }, BRIDGE <: Bridge.Of[DSL]] =
    Executor {
      val dsl: DSL
      val bridge: BRIDGE
    }

  type Ofp[DSL <: { type -⚬[A, B] }, BRIDGE <: Bridge.Of[DSL], P[_]] =
    Of[DSL, BRIDGE] { type ExecutionParam[A] = P[A] }

  trait Factory {
    type Dsl <: { type -⚬[A, B] }
    val dsl: Dsl

    type Bridge <: libretto.exec.Bridge.Of[dsl.type]
    val bridge: Bridge

    type ExecutionParam[A]

    type ExecutorResource

    def name: String
    def create(): ExecutorResource
    def access(r: ExecutorResource): Executor.Ofp[dsl.type, bridge.type, ExecutionParam]
    def shutdown(r: ExecutorResource): Unit
  }

  object Factory {
    type Of[DSL, BRIDGE] =
      Factory {
        type Dsl    <: DSL    & { type -⚬[A, B] }
        type Bridge <: BRIDGE & libretto.exec.Bridge.Of[dsl.type]
      }

    type Ofp[DSL, BRIDGE, P[_]] =
      Of[DSL, BRIDGE] { type ExecutionParam[A] = P[A] }
  }

  enum CancellationReason {
    case User(position: SourcePos)
    case Bug(message: String, cause: Option[Throwable])
  }
}
