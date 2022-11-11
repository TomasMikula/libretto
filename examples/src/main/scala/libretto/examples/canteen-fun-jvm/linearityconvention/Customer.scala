package canteen.linearityconvention

import Canteen._

class Customer(paymentCard: PaymentCard) {

  def behavior(canteen: Canteen): Unit = {
    val session = canteen.enter()

    val sectionSoup = session.proceedToSoups()

    val (soup, sectionMain)       = tryGetSoupAndGoToMain(sectionSoup)
    val (dish, sectionDessert)    = tryGetMainDishAndGoToDesserts(sectionMain)
    val (dessert, sectionPayment) = tryGetDessertAndGoToPayment(sectionDessert)

    sectionPayment.payAndClose(paymentCard)

    soup.foreach(_.eat())
    dish.foreach(_.eat())
    dessert.foreach(_.eat())
  }

  private def tryGetSoupAndGoToMain(s: SectionSoup): (Option[Soup], SectionMain) =
    s.getSoup() match {
      case Left((soup, s))    => (Some(soup), s.proceedToMainDishes())
      case Right(mainSection) => (None,       mainSection)
    }

  private def tryGetMainDishAndGoToDesserts(s: SectionMain): (Option[MainDish], SectionDessert) =
    s.getMainDish() match {
      case Left((dish, s))       => (Some(dish), s.proceedToDesserts())
      case Right(dessertSection) => (None,       dessertSection)
    }

  private def tryGetDessertAndGoToPayment(s: SectionDessert): (Option[Dessert], SectionPayment) =
    s.getDessert() match {
      case Left((dessert, s)) => (Some(dessert), s.proceedToPayment())
      case Right(paySection)  => (None,          paySection)
    }
}
