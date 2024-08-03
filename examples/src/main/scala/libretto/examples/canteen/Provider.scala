package libretto.examples.canteen

import libretto.examples.canteen.Protocol.*
import libretto.scaletto.StarterKit.*

/** A simplistic canteen facility that serves only one customer and prepares everything on demand. */
object Provider {

  def behavior: Done -⚬ Session =
    soupSection > Session.create

  def soupSection: Done -⚬ SectionSoup =
    rec { soupSection =>
      SectionSoup.from(
        onSoupRequest =
          λ { case +(done) =>
            injectL( makeSoup(done) |*| soupSection(done) )
          },
        goToMainDishes =
          mainSection,
      )
    }

  def mainSection: Done -⚬ SectionMain =
    rec { mainSection =>
      SectionMain.from(
        onDishRequest =
          λ { case +(done) =>
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
