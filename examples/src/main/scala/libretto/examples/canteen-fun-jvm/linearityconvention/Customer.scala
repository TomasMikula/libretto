package canteen.linearityconvention

import Canteen._

object Customer {

  def behavior(session: Session, card: PaymentCard): Unit =
    val sectionSoup         = session.proceedToSoups()
    val (soup, sectionMain) = tryGetSoupAndProceed(sectionSoup)
    val (dish, sectionPay)  = tryGetDishAndProceed(sectionMain)

    sectionPay.payAndClose(card)

    soup.foreach(_.eat())
    dish.foreach(_.eat())

  private def tryGetSoupAndProceed(s: SectionSoup): (Option[Soup], SectionMain) =
    s.getSoup() match
      case Left((soup, s))    => (Some(soup), s.proceedToMainDishes())
      case Right(mainSection) => (None,       mainSection)

  private def tryGetDishAndProceed(s: SectionMain): (Option[MainDish], SectionPayment) =
    s.getMainDish() match
      case Left((dish, s))   => (Some(dish), s.proceedToPayment())
      case Right(paySection) => (None,       paySection)
}
