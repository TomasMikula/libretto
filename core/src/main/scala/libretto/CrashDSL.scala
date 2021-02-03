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
  
  private val lib = CoreLib(this)
  import lib._
  
  def cocrash[A, B](msg: String): (Need |*| A) -⚬ (Need |*| B) =
    id                                   [                      Need |*| A  ]
      .introFst(lInvertSignal)        .to[ (Need |*| Done) |*| (Need |*| A) ]
      .assocLR.>.snd(XI)              .to[ Need |*| (Need |*| (Done |*| A)) ]
      .>.snd.snd(crash(msg))          .to[ Need |*| (Need |*| (Done |*| B)) ]
      .>.snd.assocRL.>.snd.fst(swap)  .to[ Need |*| ((Done |*| Need) |*| B) ]
      .>.snd(elimFst(rInvertSignal))  .to[ Need |*|                      B  ]
  
  def crashd(msg: String): Done -⚬ Done =
    id                               [ Done         ]
      .introSnd                   .to[ Done |*| One ]
      .>(crash[One, One](msg))    .to[ Done |*| One ]
      .elimSnd                    .to[ Done         ]
    
  def crashn(msg: String): Need -⚬ Need =
    id                               [ Need         ]
      .introSnd                   .to[ Need |*| One ]
      .>(cocrash[One, One](msg))  .to[ Need |*| One ]
      .elimSnd                    .to[ Need         ]
}
