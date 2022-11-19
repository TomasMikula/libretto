package libretto.examples.canteen

import libretto.examples.canteen.Protocol._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._
import libretto.scaletto.StarterKit.coreLib._
import libretto.scaletto.StarterKit.coreLib.|+|._

object Customer {

  def behavior: (Session |*| PaymentCard) -⚬ PaymentCard =
    λ { case (session |*| card) =>
      val soupSection               = Session.enter(session)
      val (soupOpt |*| mainSection) = tryGetSoupAndProceed(soupSection)
      val (dishOpt |*| paySection)  = tryGetMainDishAndProceed(mainSection)

      paySection(card)
        .waitFor(
          joinAll(
            soupOpt .map(eatSoup(_))     .getOrElse(done),
            dishOpt .map(eatMainDish(_)) .getOrElse(done),
          )
        )
    }

  private def tryGetSoupAndProceed: SectionSoup -⚬ (Maybe[Soup] |*| SectionMainDish) =
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

  private def tryGetMainDishAndProceed: SectionMainDish -⚬ (Maybe[MainDish] |*| SectionPayment) =
    λ { mainSection =>
      SectionMainDish
        .getMainDish(mainSection)
        .switch(
          caseLeft =
            λ { case (dish |*| mainSection) =>
              val paySection = SectionMainDish.proceedToPayment(mainSection)
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
