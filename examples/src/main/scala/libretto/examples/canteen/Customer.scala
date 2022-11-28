package libretto.examples.canteen

import libretto.examples.canteen.Protocol._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._
import libretto.scaletto.StarterKit.coreLib._
import libretto.scaletto.StarterKit.coreLib.|+|._

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
        .switch(
          caseLeft =
            λ { case (dish |*| mainSection) =>
              val paySection = SectionMain.proceedToPayment(mainSection)
              val someDish   = Maybe.just(dish)
              someDish |*| paySection
            },
          caseRight =
            λ { paySection =>
              val noDish = Maybe.empty[MainDish](one)
              noDish |*| paySection
            },
        )
    }

}
