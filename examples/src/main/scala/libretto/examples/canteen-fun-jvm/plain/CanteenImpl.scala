package canteen.plain

class CanteenImpl extends Canteen {
  import CanteenImpl.SessionImpl

  override def enter(): Canteen.Session =
    SessionImpl.initial()
}

object CanteenImpl {
  import Canteen._

  private class SessionImpl extends Canteen.Session {

    enum State:
      case SectionSoup
      case SectionMain
      case SectionDessert
      case SectionPayment
      case Closed

    import State._

    private var state: State = SectionSoup

    override def getSoup(): Option[Soup] =
      this.state match
        case SectionSoup =>
          val res = cookSoup()
          if (res.isEmpty)
            // proceed to SectionMain
            this.state = SectionMain
          res

        case other =>
          throw IllegalStateException(s"Cannot ask for soup in state $other")

    override def getMainDish(): Option[MainDish] =
      this.state match
        case SectionSoup =>
          this.state = SectionMain // automatically transition to SectionMain
          getMainDish()

        case SectionMain =>
          val res = cookMainDish()
          if (res.isEmpty) this.state = SectionDessert
          res

        case other =>
          throw IllegalStateException(s"Cannot ask for main dish in state $other")

    override def getDessert(): Option[Dessert] =
      this.state match {
        case SectionSoup | SectionMain =>
          this.state = SectionDessert // automatically transition to SectionDessert
          getDessert()

        case SectionDessert =>
          val res = cookDessert()
          if (res.isEmpty) {
            // forcefully proceed to SectionPayment
            this.state = SectionPayment
          }
          res

        case other =>
          throw IllegalStateException(s"Cannot ask for dessert in state $other")
      }

    override def payAndClose(card: PaymentCard): Unit =
      this.state match {
        case Closed =>
          throw IllegalStateException("Session already closed")
        case _ =>
          processPayment(card)
          this.state = Closed
      }


    private def cookSoup(): Option[Soup] =
      None // out of soup

    private def cookMainDish(): Option[MainDish] =
      Some(new MainDish())

    private def cookDessert(): Option[Dessert] =
      Some(new Dessert())

    private def processPayment(card: PaymentCard): Unit =
      ()
  }

  private object SessionImpl {
    def initial(): SessionImpl =
      new SessionImpl
  }
}
