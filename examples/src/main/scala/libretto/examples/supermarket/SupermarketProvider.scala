package libretto.examples.supermarket

import libretto.scaletto.StarterKit.*
import libretto.examples.supermarket.baskets.*
import libretto.examples.supermarket.money.*
import scala.concurrent.duration.*

object SupermarketProvider extends SupermarketInterface {
  import libretto.scaletto.StarterKit.$.*

  override val goods: Goods.type = Goods
  import goods.*

  private type BorrowedBasket = Basket |*| -[Basket]
  private type ItemSelection = Beer |&| ToiletPaper
  private type GoodsSupply = Unlimited[ItemSelection]
  private type CoinSink = Unlimited[-[Coin]]

  override opaque type Shopping[ItemsInBasket] =
    ItemsInBasket |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink))

  override opaque type Supermarket =
    Unlimited[Shopping[One]]

  override given comonoidSupermarket: Comonoid[Supermarket] =
    Unlimited.comonoidUnlimited

  override given basketReadiness[Items]: Signaling.Positive[Shopping[Items]] =
    Signaling.Positive.bySnd(using Signaling.Positive.byFst(using signalingJunctionBorrowedBasket))

  override def enterAndObtainBasket: Supermarket -⚬ Shopping[One] =
    λ { supermarket =>
      val shopping: $[Shopping[One]] =
        Unlimited.single(supermarket)

      val (empty |*| ((basket |*| negBasket) |*| (goodsSupply |*| coinSink))) =
        shopping

      // delay supply of goods until basket is obtained
      val (basket1 |*| goodsSupply1) =
        (basket |*| goodsSupply) > sequence_PN[Basket, GoodsSupply]

      val (basketNumber |*| basket2) = serialNumber(basket1)
      val basket3 = basket2 waitFor {
        basketNumber > printLine(n => s"${Console.RED}+1${Console.RESET} basket $n is now in use")
      }

      (empty |*| ((basket3 |*| negBasket) |*| (goodsSupply1 |*| coinSink)))
    }

  override def returnBasketAndLeave: Shopping[One] -⚬ One =
    λ { case (unit |*| ((basket |*| negBasket) |*| (goodsSupply |*| coinSink))) =>
      val (basketNumber |*| basket1) = serialNumber(basket)
      val basket2 = basket1 waitFor {
        basketNumber > printLine(n => s"${Console.GREEN}-1${Console.RESET} basket $n is now available")
      }
      unit
        .alsoElim(returnBasket(basket2 |*| negBasket))
        .alsoElim(closeSupply(goodsSupply))
        .alsoElim(closeCoinSink(coinSink))
    }

  override def addToiletPaperToBasket[Items]: Shopping[Items] -⚬ Shopping[ToiletPaper |*| Items] =
    addItemToBasket(chooseToiletPaper)

  override def addBeerToBasket[Items]: Shopping[Items] -⚬ Shopping[Beer |*| Items] =
    addItemToBasket(chooseBeer)

  override def payForToiletPaper[Items]: (Coin |*| Shopping[ToiletPaper |*| Items]) -⚬ (ToiletPaper |*| Shopping[Items]) =
    payForItem[ToiletPaper, Items]

  override def payForBeer[Items]: (Coin |*| Shopping[Beer |*| Items]) -⚬ (Beer |*| Shopping[Items]) =
    payForItem[Beer, Items]

  private given signalingJunctionBorrowedBasket: SignalingJunction.Positive[BorrowedBasket] =
    SignalingJunction.Positive.byFst

  private def returnBasket  : (Basket |*| -[Basket]) -⚬ One = backvert
  private def receiveBasket : One -⚬ (-[Basket] |*| Basket) = forevert

  private def chooseBeer        : ItemSelection -⚬ Beer        = chooseL
  private def chooseToiletPaper : ItemSelection -⚬ ToiletPaper = chooseR

  private def closeSupply   : GoodsSupply -⚬ One = Unlimited.discard
  private def closeCoinSink : CoinSink    -⚬ One = Unlimited.discard

  private def sendCoin: (Coin |*| CoinSink) -⚬ CoinSink =
    par(id, Unlimited.getFst) > assocRL > elimFst(money.sendCoin)

  private def supplyItem[Item: SignalingJunction.Positive](
    chooseItem: ItemSelection -⚬ Item,
  ): GoodsSupply -⚬ (Item |*| GoodsSupply) =
    λ { goodsSupply =>
      val (itemSelection |*| goodsSupply1) = Unlimited.getSome(goodsSupply)
      val item: $[Item]                    = chooseItem(itemSelection)
      (item > delayUsing(randomDelay)) |*| goodsSupply1
    }

  private def randomDelay: Done -⚬ Done =
    constVal(()) > mapVal(_ => (scala.util.Random.nextDouble * 1000 + 100).toInt.millis) > delay

  private def addItemToBasket[Item: SignalingJunction.Positive, Items](
    pick: ItemSelection -⚬ Item,
  ): Shopping[Items] -⚬ Shopping[Item |*| Items] =
    λ { case (items |*| (basket |*| (goodsSupply |*| coinSink))) =>
      // don't let the customer pick an item before basket is ready
      val (basket1 |*| goodsSupply1) =
        (basket |*| goodsSupply) > sequence_PN

      val (item |*| goodsSupply2) =
        goodsSupply1 > supplyItem(pick)

      // don't make basket ready again before item is obtained
      val (item1 |*| basket2) =
        item sequence basket1

      (item1 |*| items) |*| (basket2 |*| (goodsSupply2 |*| coinSink))
    }

  private def payForItem[
    Item: SignalingJunction.Positive,
    Items,
  ]: (Coin |*| Shopping[Item |*| Items]) -⚬ (Item |*| Shopping[Items]) =
    λ { case (coin |*| ((item |*| items) |*| (basket |*| (goodsSupply |*| coinSink)))) =>
      // prevent customer from using the item before Coin is provided
      val (item1 |*| coin1) = item sequenceAfter coin

      // prevent returning basket before purchase is paid
      val (basket1 |*| coin2) = basket sequenceAfter coin1

      item1 |*| (items |*| (basket1 |*| (goodsSupply |*| sendCoin(coin2 |*| coinSink))))
    }

  private def makeGoodsSupply: Done -⚬ (GoodsSupply |*| Done) = rec { self =>
    Unlimited.createWith[Done, ItemSelection, Done](
      case0 = id[Done],
      case1 = fork > fst(choice(produceBeer, produceToiletPaper)),
      caseN = forkMap(self, self) > IXI > snd(join),
    )
  }

  private def coinsToBank: One -⚬ (CoinSink |*| CoinBank) =
    done > Unlimited.createWith[Done, -[Coin], CoinBank](
      case0 = newCoinBank,
      case1 = newCoinBank > λ { bank => λ.closure { coin => depositCoin(coin |*| bank) } },
    )

  def openSupermarket(capacity: Int): Done -⚬ (Supermarket |*| CoinBank) =
    λ { trigger =>
      val ((trigger1 |*| trigger2) |*| one) = fork(trigger) > introSnd

      // make only as many baskets as there are permitted concurrently shopping customers
      val baskets: $[LList1[Basket]] =
        makeBaskets(capacity)(trigger1)

      // Pretend there is an infinite supply of baskets, via pooling.
      // When the pool is empty, next customer will not obtain a basket until a basket is returned to the pool.
      // `collectedBaskets` will become available once there's no chance that anyone will still use them.
      val ((basketSupply: $[Unlimited[BorrowedBasket]]) |*| (collectedBaskets: $[LList1[Basket]])) =
        baskets > Unlimited.pool

      // `goodsSupplyClosed` will signal once there's no chance that anyone still needs it.
      val ((goodsSupply: $[GoodsSupply]) |*| (goodsSupplyClosed: $[Done])) =
        makeGoodsSupply(trigger2)

      // Any coins sent to `coinSink` will appear in `coinBank`.
      val ((coinSink: $[CoinSink]) |*| (coinBank: $[CoinBank])) =
        coinsToBank(one)

      // Since `GoodsSupply` is a comonoid, it can be split arbitrarily
      // and given to an unlimited number of customers
      val unlimitedGoodsSupply: $[Unlimited[GoodsSupply]] =
        goodsSupply > Unlimited.fromComonoid

      // Since `CoinSink` is a comonoid, it can be split arbitrarily
      // and given to an unlimited number of customers
      val unlimitedCoinSinks: $[Unlimited[CoinSink]] =
        coinSink > Unlimited.fromComonoid

      val unlimitedShopping: $[Unlimited[One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink))]] = {
        import Unlimited.{zip, map}
        zip(basketSupply |*| zip(unlimitedGoodsSupply |*| unlimitedCoinSinks)) > map(introFst)
      }

      // wait for goods supply to shut down and all baskets returned before returning today's revenue
      val finalCoinBank: $[CoinBank] =
        coinBank
          .waitFor(goodsSupplyClosed)
          .waitFor(destroyBaskets(collectedBaskets))

      unlimitedShopping |*| finalCoinBank
    }
}
