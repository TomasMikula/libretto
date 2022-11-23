package canteen.plain

import Canteen._

object Customer {

  def behavior(canteen: Canteen, card: PaymentCard): Unit =
    val session = canteen.enter()

    val soup = session.getSoup()

    val dish = session.getMainDish()

    session.payAndClose(card)

    soup.foreach(_.eat())
    dish.foreach(_.eat())

  def illegalBehavior1(canteen: Canteen, card: PaymentCard): Unit = {
    val session = canteen.enter()

    val dish = session.getMainDish()

    val soup = session.getSoup()
    // 💥 Illegal: Cannot go from main dishes back to soups.
  }

  def illegalBehavior2(canteen: Canteen, card: PaymentCard): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()

    session.payAndClose(card)

    val dish = session.getMainDish()
    // 💥 Illegal: Session already closed.
  }

  def illegalBehavior3(canteen: Canteen, card: PaymentCard): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()

    soup.foreach(_.eat())

    // 👮‍♀️ Illegal: Leaving without paying.
  }

  def illegalBehavior4(canteen: Canteen, card: PaymentCard): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()
    val dish = session.getMainDish()

    session.payAndClose(card)

    dish.foreach(_.eat())

    // 👮‍♀️ Illegal: Did not eat the soup.
  }

  def illegalBehavior5(canteen: Canteen, card: PaymentCard): Unit = {
    val session = canteen.enter()

    val soup = session.getSoup()

    session.payAndClose(card)

    soup.foreach(_.eat())
    soup.foreach(_.eat())
    // 💥 Illegal: Attempting to eat the soup twice.
  }

  def illegalBehavior6(canteen: Canteen, card: PaymentCard): Unit = {
    val session = canteen.enter()

    val soup1: Option[Soup] = session.getSoup() // None
    val soup2: Option[Soup] = session.getSoup()
    // 💥 Illegal if the first attempt returned `None`.
  }
}
