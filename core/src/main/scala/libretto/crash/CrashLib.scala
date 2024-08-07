package libretto.crash

import libretto.puro.PuroLib

object CrashLib {
  def apply(
    dsl: CrashDSL,
  )
  : CrashLib[dsl.type] =
    new CrashLib(dsl)
}

class CrashLib[
  DSL <: CrashDSL,
](
  val dsl: DSL,
) { lib =>
  import dsl.*

  private val puroLib = PuroLib(dsl)
  import puroLib.*

  def leftOrCrash[A, B](msg: String = "Expected Left, was Right"): (A |+| B) -⚬ A =
    |+|.signalR > either(id[A], crashWhenDone[B, A](msg))

  def rightOrCrash[A, B](msg: String = "Expected Right, was Left"): (A |+| B) -⚬ B =
    |+|.signalL > either(crashWhenDone[A, B](msg), id[B])
}