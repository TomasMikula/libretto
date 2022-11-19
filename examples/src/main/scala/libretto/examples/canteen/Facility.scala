package libretto.examples.canteen

import libretto.examples.canteen.Protocol._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._

/** A simplistic canteen facility that serves only one customer and prepares everything on demand. */
object Facility {

  def behavior: Done -⚬ Session =
    Session.from(soupSection)

  def soupSection: Done -⚬ SectionSoup =
    rec { soupSection =>
      SectionSoup.from(
        onSoupRequest =
          λ.+ { done =>
            injectL( makeSoup(done) |*| soupSection(done) )
          },
        goToMainDishes =
          mainSection,
      )
    }

  def mainSection: Done -⚬ SectionMainDish =
    rec { mainSection =>
      SectionMainDish.from(
        onDishRequest =
          λ.+ { done =>
            injectL( makeMainDish(done) |*| mainSection(done) )
          },
        goToPayment =
          paymentSection,
      )
    }

  def paymentSection: Done -⚬ SectionPayment =
    λ { done =>
      λ.closure { card =>
        card.waitFor(done)
      }
    }
}
