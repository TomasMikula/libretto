package libretto.crash

import libretto.core.{CoreDSL, CoreLib}

trait CrashDSL extends CoreDSL {
  /** Starts propagating an error downstream (which might be through both the in-port and the out-port).
    *
    * Use only for irrecoverable errors.
    * Recoverable errors should be expressed in function signature
    * and handled appropriately.
    *
    * [[Done]] on the in-port is the trigger to crash.
    * [[A]] on the in-port allows to consume any unhandled resources.
    * [[B]] on the out-port allows to fulfill any obligation to produce resources.
    */
  def crashWhenDone[A, B](msg: String): (Done |*| A) -⚬ B

  private val lib = CoreLib(this)
  import lib.*

  def crashWhenNeed[A, B](msg: String): A -⚬ (Need |*| B) =
    introFst(lInvertSignal) > assocLR > snd(crashWhenDone(msg))

  def crashNow[A, B](msg: String): A -⚬ B =
    introFst(done) > crashWhenDone(msg)

  def crashd(msg: String): Done -⚬ Done =
    introSnd > crashWhenDone(msg)

  def crashn(msg: String): Need -⚬ Need =
    crashWhenNeed(msg) > elimSnd
}
