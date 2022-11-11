package canteen.plain

import Canteen.PaymentCard

object Main {
  def main(args: Array[String]): Unit = {
    val canteen = new CanteenImpl
    val customer = new Customer(new PaymentCard("1234 5678 9876 5432"))

    customer.visitCanteen(canteen)

    // customer.illegalBehavior1(canteen)
    // customer.illegalBehavior2(canteen)
    // customer.illegalBehavior3(canteen)
    // customer.illegalBehavior4(canteen)
    // customer.illegalBehavior5(canteen)
    // customer.illegalBehavior6(canteen)
  }
}
