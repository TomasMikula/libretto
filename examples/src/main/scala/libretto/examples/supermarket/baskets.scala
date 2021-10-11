package libretto.examples.supermarket

import libretto.StarterKit._

object baskets {
  opaque type Basket = Done

  def makeBasket: Done -⚬ Basket =
    id

  def destroyBasket: Basket -⚬ Done =
    id

  def returnBasket: (Basket |*| -[Basket]) -⚬ One =
    backvert

  def receiveBasket: One -⚬ (-[Basket] |*| Basket) =
    forevert

  def makeBaskets(n: Int): Done -⚬ LList1[Basket] = {
    require(n >= 1)
    n match {
      case 1 => makeBasket > LList1.singleton[Done]
      case _ => forkMap(makeBasket, makeBaskets(n - 1)) > LList1.cons1
    }
  }

  def destroyBaskets: LList1[Basket] -⚬ Done =
    LList1.foldMap(destroyBasket)

  implicit def signalingJunctionBasket: SignalingJunction.Positive[Basket] =
    SignalingJunction.Positive.signalingJunctionPositiveDone
}
