package canteen.plain

trait Canteen {
  def enter(): Canteen.Session
}

object Canteen {

  trait Session {
    def getSoup(): Option[Soup]

    def getMainDish(): Option[MainDish]

    def payAndClose(card: PaymentCard): Unit
  }

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
