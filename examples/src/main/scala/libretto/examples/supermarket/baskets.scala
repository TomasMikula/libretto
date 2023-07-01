package libretto.examples.supermarket

import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.scalettoLib.given

object baskets {
  opaque type Basket = Val[Int]

  def makeBasket(sn: Int): Done -⚬ Basket =
    constVal(sn)

  def serialNumber: Basket -⚬ (Val[Int] |*| Basket) =
    dup

  def destroyBasket: Basket -⚬ Done =
    neglect

  def makeBaskets(n: Int): Done -⚬ LList1[Basket] = {
    require(n >= 1)
    n match {
      case 1 => makeBasket(1) > LList1.singleton[Basket]
      case n => forkMap(makeBasket(n), makeBaskets(n - 1)) > LList1.cons1
    }
  }

  def destroyBaskets: LList1[Basket] -⚬ Done =
    LList1.foldMap(destroyBasket)

  given SignalingJunction.Positive[Basket] =
    signalingJunctionPositiveVal
}
