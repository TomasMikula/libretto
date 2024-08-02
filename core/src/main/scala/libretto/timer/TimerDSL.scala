package libretto.timer

import libretto.puro.{Puro, PuroLib}
import scala.concurrent.duration.FiniteDuration

trait TimerDSL extends Puro {
  def delay(d: FiniteDuration): Done -⚬ Done

  private val lib = PuroLib(this)
  import lib.*

  def delayNeed(d: FiniteDuration): Need -⚬ Need = {
    id                               [                      Need  ]
      .>(introFst(lInvertSignal)) .to[ (Need |*|  Done) |*| Need  ]
      .>.fst.snd(delay(d))        .to[ (Need |*|  Done) |*| Need  ]
      .>(assocLR)                 .to[  Need |*| (Done  |*| Need) ]
      .>(elimSnd(rInvertSignal))  .to[  Need                      ]
  }
}
