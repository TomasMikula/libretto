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

  private def tryGetSoupAndProceed: StageSoup -⚬ (Maybe[Soup] |*| StageMainDish) =
    λ { soupSection =>
      StageSoup
        .getSoup(soupSection)
        .switch(
          caseLeft =
            λ { case (soup |*| soupSection) =>
              val mainSection = StageSoup.proceedToNextStage(soupSection)
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

  private def tryGetMainDishAndProceed: StageMainDish -⚬ (Maybe[MainDish] |*| StageDessert) =
    λ { mainSection =>
      StageMainDish
        .getMainDish(mainSection)
        .switch(
          caseLeft =
            λ { case (dish |*| mainSection) =>
              val dessertSection = StageMainDish.proceedToNextStage(mainSection)
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

  private def tryGetDessertAndProceed: StageDessert -⚬ (Maybe[Dessert] |*| StagePayment) =
    λ { dessertSection =>
      StageDessert
        .getDessert(dessertSection)
        .switch(
          caseLeft =
            λ { case (dessert |*| dessertSection) =>
              val paymentSection = StageDessert.proceedToNextStage(dessertSection)
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
