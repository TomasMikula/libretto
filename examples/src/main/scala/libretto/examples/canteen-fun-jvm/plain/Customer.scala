package canteen.plain

import Canteen._

class Customer(paymentCard: PaymentCard) {

  def visitCanteen(canteen: Canteen): Unit =
    val session = canteen.enter()

    val soup = session.getSoup()

    val dish = session.getMainDish()

    val dessert = session.getDessert()

    session.payAndClose(paymentCard)

    soup   .foreach(_.eat())
    dish   .foreach(_.eat())
    dessert.foreach(_.eat())

  def illegalBehavior1(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val dish = session.getMainDish()

    val soup = session.getSoup()
    // 💥 Illegal: Cannot go from main dishes back to soups.
  }

  def illegalBehavior2(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()

    session.payAndClose(paymentCard)

    val dish = session.getMainDish()
    // 💥 Illegal: Session already closed.
  }

  def illegalBehavior3(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()

    soup.foreach(_.eat())

    // 👮‍♀️ Illegal: Leaving without paying.
  }

  def illegalBehavior4(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()
    val dish = session.getMainDish()

    session.payAndClose(paymentCard)

    dish.foreach(_.eat())

    // 👮‍♀️ Illegal: Did not eat the soup.
  }

  def illegalBehavior5(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val dessert = session.getDessert()

    session.payAndClose(paymentCard)

    dessert.foreach(_.eat())
    dessert.foreach(_.eat())
    // 💥 Illegal: Attempting to eat the dessert twice.
  }

  def illegalBehavior6(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val soup1: Option[Soup] = session.getSoup() // None
    val soup2: Option[Soup] = session.getSoup()
    // 💥 Illegal if the first attempt returned `None`.
  }
}
