package libretto.examples.supermarket

import libretto.scaletto.StarterKit._
import libretto.scaletto.StarterKit.scalettoLib.given

object money {
  opaque type Coin = Done
  opaque type CoinBank = Val[Int] // number of coins

  def forgeCoin: Done -⚬ Coin =
    id[Done]

  def sendCoin: (Coin |*| -[Coin]) -⚬ One =
    backvert

  def receiveCoin: One -⚬ (-[Coin] |*| Coin) =
    forevert

  def newCoinBank: Done -⚬ CoinBank =
    constVal(0)

  def openCoinBank: CoinBank -⚬ Val[Int] =
    id

  def depositCoin: (Coin |*| CoinBank) -⚬ CoinBank =
    awaitPosFst[CoinBank] > mapVal(_ + 1)

  given SignalingJunction.Positive[Coin] =
    SignalingJunction.Positive. signalingJunctionPositiveDone

  given Junction.Positive[CoinBank] =
    junctionVal

  given Semigroup[CoinBank] with {
    override def combine: (CoinBank |*| CoinBank) -⚬ CoinBank =
      unliftPair > mapVal { case (a, b) => a + b }
  }
}
