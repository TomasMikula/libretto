package libretto.examples.canteen

import libretto.examples.canteen.Protocol.*
import libretto.scaletto.StarterApp
import libretto.scaletto.StarterKit.*

object Main extends StarterApp {

  override def blueprint: Done -⚬ Done =
    λ.+ { started =>
      val paymentCard  = started > PaymentCard.issue
      val session      = Provider.behavior(started)
      val paymentCard1 = Customer.behavior(session |*| paymentCard)
      PaymentCard.shred(paymentCard1)
    }

}
