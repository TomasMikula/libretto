package libretto.examples.canteen

import libretto.examples.canteen.Protocol._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._

/** A simplistic canteen facility that serves only one customer and prepares everything on demand. */
object Facility {

  def behavior: Done -⚬ Session =
    Session.from(soupSection)

  def soupSection: Done -⚬ StageSoup =
    rec { soupSection =>
      StageSoup.from(
        onSoupRequest =
          λ.+ { done =>
            injectL( cookSoup(done) |*| soupSection(done) )
          },
        goToNextStage =
          mainSection,
      )
    }

  def mainSection: Done -⚬ StageMainDish =
    rec { mainSection =>
      StageMainDish.from(
        onDishRequest =
          λ.+ { done =>
            injectL( cookMainDish(done) |*| mainSection(done) )
          },
        goToNextStage =
          dessertSection,
      )
    }

  def dessertSection: Done -⚬ StageDessert =
    rec { dessertSection =>
      StageDessert.from(
        onDessertRequest =
          λ.+ { done =>
            injectL( cookDessert(done) |*| dessertSection(done) )
          },
        goToNextStage =
          paymentSection,
      )
    }

  def paymentSection: Done -⚬ StagePayment =
    λ { done =>
      λ.closure { card =>
        card.waitFor(done)
      }
    }

  def cookSoup: Done -⚬ Soup =
    printLine("Cooking soup") > constVal("Soup")

  def cookMainDish: Done -⚬ MainDish =
    printLine("Cooking main dish") > constVal("MainDish")

  def cookDessert: Done -⚬ Dessert =
    printLine("Cooking dessert") > constVal("Dessert")
}
