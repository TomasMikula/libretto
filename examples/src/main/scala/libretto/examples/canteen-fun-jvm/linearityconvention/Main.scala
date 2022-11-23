package canteen.linearityconvention

import Canteen.PaymentCard

object Main {
  def main(args: Array[String]): Unit = {
    val canteen = new CanteenImpl
    val session = canteen.enter()
    val card = new PaymentCard("1234 5678 9876 5432")

    Customer.behavior(session, card)
  }
}
