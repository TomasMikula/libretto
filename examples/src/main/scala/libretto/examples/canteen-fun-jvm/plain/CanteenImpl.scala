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

        case SectionMain | SectionPayment | Closed =>
          throw IllegalStateException(s"Cannot ask for soup in state $state")

    override def getMainDish(): Option[MainDish] =
      this.state match
        case SectionSoup =>
          this.state = SectionMain // automatically transition to SectionMain
          getMainDish()

        case SectionMain =>
          val res = cookMainDish()
          if (res.isEmpty) {
            // forcefully proceed to SectionPayment
            this.state = SectionPayment
          }
          res

        case SectionPayment | Closed =>
          throw IllegalStateException(s"Cannot ask for main dish in state $state")

    override def payAndClose(card: PaymentCard): Unit =
      this.state match {
        case SectionPayment | SectionMain | SectionSoup =>
          processPayment(card)
          this.state = Closed
        case Closed =>
          throw IllegalStateException("Session already closed")
      }


    private def cookSoup(): Option[Soup] =
      None // out of soup

    private def cookMainDish(): Option[MainDish] =
      Some(new MainDish())

    private def processPayment(card: PaymentCard): Unit =
      ()
  }

  private object SessionImpl {
    def initial(): SessionImpl =
      new SessionImpl
  }
}
