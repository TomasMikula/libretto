package libretto.examples.supermarket

import libretto.StarterKit._
import libretto.examples.supermarket.money._
import scala.concurrent.duration._

object Customers {
  def apply(supermarket: SupermarketInterface): Customers[supermarket.type] =
    new Customers(supermarket)
}

class Customers[SupermarketImpl <: SupermarketInterface](
  val supermarket: SupermarketImpl,
) {
  import libretto.StarterKit.$._
  import supermarket._
  import supermarket.goods._

  /** Blueprint for customer behavior. A customer gets access to a supermarket and runs to completion ([[Done]]). */
  def behavior(who: String): Supermarket -⚬ Done = {
    def getCoins: Done -⚬ (Coin |*| (Coin |*| Coin)) =
      printLine(s"🪙 $who is forging 3 coins") > λ { trigger =>
        val (trigger1 |*| (trigger2 |*| trigger3)) = forkMap(id, fork)(trigger)
        forgeCoin(trigger1) |*| (forgeCoin(trigger2) |*| forgeCoin(trigger3))
      }

    def useTP = delayUsing[ToiletPaper](randomDelay) > useToiletPaper
    def drink = delayUsing[Beer       ](randomDelay) > drinkBeer

    λ { (supermarket: $[Supermarket]) =>
      val ((shopping) |*| (basketObtained)) =
        enterAndObtainBasket(supermarket) > basketReadiness.signalDone

      val logged: $[Done] =
        when(basketObtained) {
          printLine(s"$who obtained a shopping basket")
        }

      val (shopping1 |*| beerAdded) =
        shopping > addBeerToBasket > addBeerToBasket > basketReadiness.signalDone

      val logged1: $[Done] =
        when(join(logged |*| beerAdded)) {
          printLine(s"$who added 2 beers to the basket")
        }

      val (shopping2 |*| tpAdded) =
        shopping1 > addToiletPaperToBasket > basketReadiness.signalDone

      val logged2: $[Done] =
        when(join(logged1 |*| tpAdded)) {
          printLine(s"$who added toilet paper to the basket")
        }

      val (coin1 |*| (coin2 |*| coin3)) =
        when(logged2) { getCoins }

      val (tp |*| shopping3) =
        payForToiletPaper(coin1 |*| shopping2)

      val (beer1 |*| shopping4) =
        payForBeer(coin2 |*| shopping3)

      val (beer2 |*| shopping5) =
        payForBeer(coin3 |*| shopping4)

      val (shopping6 |*| paid) =
        shopping5 > basketReadiness.signalDone

      val logged3: $[Done] =
        when(paid) {
          printLine(s"$who paid for the purchase")
        }

      val shoppingFinished: $[Done] =
        (returnBasketAndLeave(shopping6) |*| logged3) > elimFst >
          printLine(s"$who returned the basket")

      val beer1Drunk: $[Done] =
        drink(beer1 waitFor shoppingFinished) > printLine(s"🍺 $who drank the 1st beer")

      val beer2Drunk: $[Done] =
        drink(beer2 waitFor beer1Drunk) > printLine(s"🍺 $who drank the 2nd beer")

      useTP(tp waitFor beer2Drunk) > printLine(s"🧻 $who used the toilet paper")
    }
  }

  private def randomDelay: Done -⚬ Done =
    constVal(()) > mapVal(_ => (scala.util.Random.nextDouble * 1000 + 100).toInt.millis) > delay
}
