package libretto.examples.canteen

import libretto.examples.canteen.Protocol._
import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.$._
import libretto.scaletto.StarterKit.coreLib._
import libretto.scaletto.StarterKit.coreLib.|+|._

object Customer {

  def behavior: (Session |*| PaymentCard) -⚬ PaymentCard =
    λ { case (session |*| card) =>
      val soupSection                     = Session.enter(session)
      val (soupOpt |*| mainSection)       = tryGetSoupAndProceed(soupSection)
      val (dishOpt |*| dessertSection)    = tryGetMainDishAndProceed(mainSection)
      val (dessertOpt |*| paymentSection) = tryGetDessertAndProceed(dessertSection)

      paymentSection(card)
        .waitFor(
          joinAll(
            soupOpt    .map(eatSoup(_))     .getOrElse(done),
            dishOpt    .map(eatMainDish(_)) .getOrElse(done),
            dessertOpt .map(eatDessert(_))  .getOrElse(done),
          )
        )
    }

  private def tryGetSoupAndProceed: SectionSoup -⚬ (Maybe[Soup] |*| SectionMainDish) =
    λ { soupSection =>
      SectionSoup
        .getSoup(soupSection)
        .switch(
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
    }

  private def tryGetMainDishAndProceed: SectionMainDish -⚬ (Maybe[MainDish] |*| SectionDessert) =
    λ { mainSection =>
      SectionMainDish
        .getMainDish(mainSection)
        .switch(
          caseLeft =
            λ { case (dish |*| mainSection) =>
              val dessertSection = SectionMainDish.proceedToDesserts(mainSection)
              val someDish       = Maybe.just(dish)
              someDish |*| dessertSection
            },
          caseRight =
            λ { dessertSection =>
              val noDish = Maybe.empty[MainDish](one)
              noDish |*| dessertSection
            },
        )
    }

  private def tryGetDessertAndProceed: SectionDessert -⚬ (Maybe[Dessert] |*| SectionPayment) =
    λ { dessertSection =>
      SectionDessert
        .getDessert(dessertSection)
        .switch(
          caseLeft =
            λ { case (dessert |*| dessertSection) =>
              val paymentSection = SectionDessert.proceedToPayment(dessertSection)
              val someDessert    = Maybe.just(dessert)
              someDessert |*| paymentSection
            },
          caseRight =
            λ { paymentSection =>
              val noDessert = Maybe.empty[Dessert](one)
              noDessert |*| paymentSection
            },
        )
    }

}
