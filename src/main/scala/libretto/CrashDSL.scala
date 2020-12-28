package libretto

trait CrashDSL extends CoreDSL {
  /** Crashes the program. Use only for irrecoverable errors.
    * 
    * Recoverable errors should be expressed in function signature
    * and handled appropriately.
    * 
    * [[Done]] in the input is the trigger to crash.
    * [[Done]] in the output is an obligation to propagate the crash.
    * [[A]] in the input allows to consume any unhandled resources.
    * [[B]] in the output allows to fulfill any obligation to produce resources.
    */
  def crash[A, B](msg: String): (Done |*| A) -⚬ (Done |*| B)
  
  def crashd(msg: String): Done -⚬ Done =
    andThen(andThen(introSnd[Done], crash[One, One](msg)), elimSnd[Done])
}
