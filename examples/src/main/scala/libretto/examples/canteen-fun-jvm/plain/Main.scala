package canteen.plain

import Canteen.PaymentCard

object Main {
  def main(args: Array[String]): Unit = {
    val canteen = new CanteenImpl
    val card = new PaymentCard("1234 5678 9876 5432")

    Customer.behavior(canteen, card)

    // Customer.illegalBehavior1(canteen, card)
    // Customer.illegalBehavior2(canteen, card)
    // Customer.illegalBehavior3(canteen, card)
    // Customer.illegalBehavior4(canteen, card)
    // Customer.illegalBehavior5(canteen, card)
    // Customer.illegalBehavior6(canteen, card)
  }
}
