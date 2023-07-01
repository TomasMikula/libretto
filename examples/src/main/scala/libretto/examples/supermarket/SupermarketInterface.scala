package libretto.examples.supermarket

import libretto.scaletto.StarterKit._
import libretto.examples.supermarket.money._

trait SupermarketInterface {
  type Supermarket
  type Shopping[Items]

  val goods: GoodsConsumer

  import goods.{Beer, ToiletPaper}

  given comonoidSupermarket: Comonoid[Supermarket]
  given basketReadiness[Items]: Signaling.Positive[Shopping[Items]]

  def enterAndObtainBasket: Supermarket -⚬ Shopping[One]

  def addBeerToBasket       [Items]: Shopping[Items] -⚬ Shopping[Beer        |*| Items]
  def addToiletPaperToBasket[Items]: Shopping[Items] -⚬ Shopping[ToiletPaper |*| Items]

  def payForBeer       [Items]: (Coin |*| Shopping[Beer        |*| Items]) -⚬ (Beer        |*| Shopping[Items])
  def payForToiletPaper[Items]: (Coin |*| Shopping[ToiletPaper |*| Items]) -⚬ (ToiletPaper |*| Shopping[Items])

  def returnBasketAndLeave: Shopping[One] -⚬ One
}
