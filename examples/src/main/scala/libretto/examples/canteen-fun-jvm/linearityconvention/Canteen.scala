package canteen.linearityconvention

trait Canteen:
  def enter(): Canteen.Session

object Canteen {

  trait Session:
    def proceedToSoups(): SectionSoup

  trait SectionSoup:
    def getSoup(): Either[(Soup, SectionSoup), SectionMain]
    def proceedToMainDishes(): SectionMain

  trait SectionMain:
    def getMainDish(): Either[(MainDish, SectionMain), SectionPayment]
    def proceedToPayment(): SectionPayment

  trait SectionPayment:
    def payAndClose(card: PaymentCard): Unit

  abstract class Meal {
    private var consumed: Boolean = false

    def eat(): Unit =
      if (!consumed) {
        println(s"Eating ${this.getClass.getSimpleName}")
        consumed = true
      } else {
        throw IllegalStateException("Already consumed")
      }
  }
  class Soup extends Meal
  class MainDish extends Meal

  case class PaymentCard(number: String)
}
