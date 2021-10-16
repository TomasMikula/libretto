package libretto.examples.supermarket

import libretto.StarterKit._
import libretto.examples.supermarket.baskets._
import libretto.examples.supermarket.goods._
import libretto.examples.supermarket.money._

object SupermarketProvider extends SupermarketInterface {
  import libretto.StarterKit.$._

  private type BorrowedBasket = Basket |*| -[Basket]
  private type ItemSelection = Beer |&| ToiletPaper
  private type GoodsSupply = Unlimited[ItemSelection]
  private type CoinSink = Unlimited[-[Coin]]

  override opaque type Shopping[ItemsInBasket] =
    ItemsInBasket |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink))

  override opaque type Supermarket =
    Unlimited[Shopping[One]]

  override implicit def comonoidSupermarket: Comonoid[Supermarket] =
    Unlimited.comonoidUnlimited

  override def basketReadiness[Items]: Signaling.Positive[Shopping[Items]] =
    Signaling.Positive.bySnd(Signaling.Positive.byFst(signalingJunctionBorrowedBasket))

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
    λ { case (one |*| ((basket |*| negBasket) |*| (goodsSupply |*| coinSink))) =>
      val (basketNumber |*| basket1) = serialNumber(basket)
      val basket2 = basket1 waitFor {
        basketNumber > printLine(n => s"${Console.GREEN}-1${Console.RESET} basket $n is now available")
      }
      List(
        returnBasket(basket2 |*| negBasket),
        closeSupply(goodsSupply),
        closeCoinSink(coinSink),
      ).foldLeft(one)((x, y) => (x |*| y) > elimFst)
    }

  override def addToiletPaperToBasket[Items]: Shopping[Items] -⚬ Shopping[ToiletPaper |*| Items] =
    addItemToBasket(chooseToiletPaper)

  override def addBeerToBasket[Items]: Shopping[Items] -⚬ Shopping[Beer |*| Items] =
    addItemToBasket(chooseBeer)

  override def payForToiletPaper[Items]: (Coin |*| Shopping[ToiletPaper |*| Items]) -⚬ (ToiletPaper |*| Shopping[Items]) =
    payForItem[ToiletPaper, Items]

  override def payForBeer[Items]: (Coin |*| Shopping[Beer |*| Items]) -⚬ (Beer |*| Shopping[Items]) =
    payForItem[Beer, Items]

  private implicit def signalingJunctionBorrowedBasket: SignalingJunction.Positive[BorrowedBasket] =
    SignalingJunction.Positive.byFst

  private def returnBasket  : (Basket |*| -[Basket]) -⚬ One = backvert
  private def receiveBasket : One -⚬ (-[Basket] |*| Basket) = forevert

  private def chooseBeer        : ItemSelection -⚬ Beer        = chooseL
  private def chooseToiletPaper : ItemSelection -⚬ ToiletPaper = chooseR

  private def closeSupply   : GoodsSupply -⚬ One = Unlimited.discard
  private def closeCoinSink : CoinSink    -⚬ One = Unlimited.discard

  private def sendCoin: (Coin |*| CoinSink) -⚬ CoinSink =
    par(id, Unlimited.getFst) > assocRL > elimFst(money.sendCoin)

  private def supplyItem[Item](chooseItem: ItemSelection -⚬ Item): GoodsSupply -⚬ (Item |*| GoodsSupply) =
    Unlimited.getFst > fst(chooseItem)

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
      case1 = newCoinBank > introFst(receiveCoin) > assocLR > snd(depositCoin),
    )

  def openSupermarket(capacity: Int): Done -⚬ (Supermarket |*| CoinBank) =
    id                                   [                                                Done                                                       ]
      .>(fork)                        .to[                          Done                  |*|               Done                                     ]
      .>(fst(makeBaskets(capacity)))  .to[                      LList1[Basket]            |*|               Done                                     ]
      .>(fst(pool))                   .to[ (Unlimited[BorrowedBasket] |*| LList1[Basket]) |*|               Done                                     ]
      .>(snd(makeGoodsSupply))        .to[ (Unlimited[BorrowedBasket] |*| LList1[Basket]) |*|  (GoodsSupply |*| Done)                                ]
      .>(snd(introSnd(coinsToBank)))  .to[ (Unlimited[BorrowedBasket] |*| LList1[Basket]) |*| ((GoodsSupply |*| Done)  |*|  (CoinSink |*| CoinBank)) ]
      .>(snd(IXI > snd(awaitPosFst))) .to[ (Unlimited[BorrowedBasket] |*| LList1[Basket]) |*| ((GoodsSupply |*| CoinSink)   |*|           CoinBank ) ]
      .>(IXI)                         .to[ (Unlimited[BorrowedBasket] |*| (GoodsSupply |*| CoinSink)) |*| (LList1[Basket]   |*|           CoinBank ) ]
      .>(snd(fst(destroyBaskets)))    .to[ (Unlimited[BorrowedBasket] |*| (GoodsSupply |*| CoinSink)) |*| (     Done        |*|           CoinBank ) ]
      .>(snd(awaitPosFst))            .to[ (Unlimited[BorrowedBasket] |*| (GoodsSupply |*| CoinSink)) |*|                                 CoinBank   ]
      .>(fst(snd(id                                                      [ GoodsSupply |*| CoinSink                       ]
        .>(par(Unlimited.fromComonoid, Unlimited.fromComonoid))      .to [ Unlimited[GoodsSupply] |*| Unlimited[CoinSink] ]
      )))                             .to[ (Unlimited[BorrowedBasket] |*| (Unlimited[GoodsSupply] |*| Unlimited[CoinSink])) |*|           CoinBank   ]
      .>(fst(snd(Unlimited.zip)))     .to[ (Unlimited[BorrowedBasket] |*| (Unlimited[GoodsSupply  |*|           CoinSink])) |*|           CoinBank   ]
      .>(fst(Unlimited.zip))          .to[  Unlimited[BorrowedBasket  |*| (          GoodsSupply  |*|           CoinSink )] |*|           CoinBank   ]
      .>(fst(Unlimited.map(introFst))).to[  Unlimited[One |*| (BorrowedBasket |*| (  GoodsSupply  |*|           CoinSink))] |*|           CoinBank   ]
}
