package libretto.examples.canteen

import libretto.examples.canteen.Protocol.*
import libretto.scaletto.StarterKit.*
import libretto.scaletto.StarterKit.$.*
import libretto.scaletto.StarterKit.coreLib.*

object Customer {

  def behavior: (Session |*| PaymentCard) -⚬ PaymentCard =
    λ { case (session |*| card) =>
      val soupSection               = Session.proceedToSoups(session)
      val (soupOpt |*| mainSection) = tryGetSoupAndProceed(soupSection)
      val (dishOpt |*| paySection)  = tryGetDishAndProceed(mainSection)

      paySection(card)
        .waitFor(
          joinAll(
            soupOpt .map(eatSoup(_))     .getOrElse(done),
            dishOpt .map(eatMainDish(_)) .getOrElse(done),
          )
        )
    }

  private def tryGetSoupAndProceed: SectionSoup -⚬ (Maybe[Soup] |*| SectionMain) =
    SectionSoup.getSoup > either(
      caseLeft =
        λ { case (soup |*| soupSection) =>
          val mainSection = SectionSoup.proceedToMainDishes(soupSection)
          val someSoup    = Maybe.just(soup)
          someSoup |*| mainSection
        },
      caseRight =
        λ { mainSection =>
          val noSoup = Maybe.empty[Soup](one)
          noSoup |*| mainSection
        },
    )

  private def tryGetDishAndProceed: SectionMain -⚬ (Maybe[MainDish] |*| SectionPayment) =
    λ { mainSection =>
      SectionMain
        .getMainDish(mainSection)
        .either {
          case Left(dish |*| mainSection) =>
            val paySection = SectionMain.proceedToPayment(mainSection)
            val someDish   = Maybe.just(dish)
            someDish |*| paySection
          case Right(paySection) =>
            val noDish = Maybe.empty[MainDish](one)
            noDish |*| paySection
        }
    }

}
