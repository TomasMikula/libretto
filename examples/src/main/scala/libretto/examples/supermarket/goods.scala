package libretto.examples.supermarket

import libretto.StarterKit._

object goods {
  // Our supermarket specializes on the most wanted items in a pandemic,
  // namely toilet paper and beer.
  opaque type ToiletPaper = Done
  opaque type Beer = Done

  def produceToiletPaper: Done -⚬ ToiletPaper =
    id[Done]

  def produceBeer: Done -⚬ Beer =
    id[Done]

  def useToiletPaper: ToiletPaper -⚬ Done =
    id[Done]

  def drinkBeer: Beer -⚬ Done =
    id[Done]

  implicit def signalingJunctionToiletPaper: SignalingJunction.Positive[ToiletPaper] =
    SignalingJunction.Positive.signalingJunctionPositiveDone

  implicit def signalingJunctionBeer: SignalingJunction.Positive[Beer] =
    SignalingJunction.Positive.signalingJunctionPositiveDone
}
