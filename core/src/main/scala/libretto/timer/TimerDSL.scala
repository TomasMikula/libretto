package libretto.timer

import libretto.core.{CoreDSL, CoreLib}
import scala.concurrent.duration.FiniteDuration

trait TimerDSL extends CoreDSL {
  def delay(d: FiniteDuration): Done -⚬ Done

  private val lib = CoreLib(this)
  import lib.*

  def delayNeed(d: FiniteDuration): Need -⚬ Need = {
    id                               [                      Need  ]
      .>(introFst(lInvertSignal)) .to[ (Need |*|  Done) |*| Need  ]
      .>.fst.snd(delay(d))        .to[ (Need |*|  Done) |*| Need  ]
      .>(assocLR)                 .to[  Need |*| (Done  |*| Need) ]
      .>(elimSnd(rInvertSignal))  .to[  Need                      ]
  }
}
