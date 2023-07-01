package libretto.examples.supermarket

import libretto.scaletto.StarterKit._

/** Our supermarket specializes in the most wanted items in a pandemic,
  * namely toilet paper and beer.
  */
trait AbstractGoods {
  type ToiletPaper
  type Beer

  given signalingJunctionToiletPaper: SignalingJunction.Positive[ToiletPaper]
  given signalingJunctionBeer:        SignalingJunction.Positive[Beer]
}

trait GoodsProducer extends AbstractGoods {
  def produceToiletPaper: Done -⚬ ToiletPaper
  def produceBeer:        Done -⚬ Beer
}

trait GoodsConsumer extends AbstractGoods {
  def useToiletPaper: ToiletPaper -⚬ Done
  def drinkBeer:      Beer        -⚬ Done
}

object Goods extends GoodsProducer with GoodsConsumer {
  override opaque type ToiletPaper = Done
  override opaque type Beer        = Done

  override given signalingJunctionToiletPaper: SignalingJunction.Positive[ToiletPaper] =
    SignalingJunction.Positive.signalingJunctionPositiveDone

  override given signalingJunctionBeer: SignalingJunction.Positive[Beer] =
    SignalingJunction.Positive.signalingJunctionPositiveDone

  override def produceToiletPaper: Done -⚬ ToiletPaper =
    id[Done]

  override def produceBeer: Done -⚬ Beer =
    id[Done]

  def useToiletPaper: ToiletPaper -⚬ Done =
    id[Done]

  def drinkBeer: Beer -⚬ Done =
    id[Done]
}
