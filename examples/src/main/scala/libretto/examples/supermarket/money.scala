package libretto.examples.supermarket

import libretto.scaletto.StarterKit._

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

  implicit def signalingJunctionCoin: SignalingJunction.Positive[Coin] =
      SignalingJunction.Positive. signalingJunctionPositiveDone

  implicit def junctionCoinBank: Junction.Positive[CoinBank] =
      junctionVal

  implicit def semigroupCoinBank: Semigroup[CoinBank] =
      new Semigroup[CoinBank] {
      override def combine: (CoinBank |*| CoinBank) -⚬ CoinBank =
          unliftPair > mapVal { case (a, b) => a + b }
      }
}
