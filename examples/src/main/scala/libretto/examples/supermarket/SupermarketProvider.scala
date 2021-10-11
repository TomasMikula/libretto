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

  override def enterAndObtainBasket: Supermarket -⚬ Shopping[One] = {
    val delaySupply: (BorrowedBasket |*| GoodsSupply) -⚬ (BorrowedBasket |*| GoodsSupply) =
      fst(swap) > assocLR > snd(sequence_PN[Basket, GoodsSupply]) > assocRL > fst(swap)

    id                             [      Supermarket                                        ]
                                .to[ Unlimited[Shopping[One]]                                ]
      .>(Unlimited.single)      .to[           Shopping[One]                                 ]
                                .to[ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
      .>(snd(assocRL))          .to[ One |*| ((BorrowedBasket |*| GoodsSupply) |*| CoinSink) ]
      .>(snd(fst(delaySupply))) .to[ One |*| ((BorrowedBasket |*| GoodsSupply) |*| CoinSink) ]
      .>(snd(assocLR))          .to[ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
  }

  override def returnBasketAndLeave: Shopping[One] -⚬ One =
    id                             [ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
      .>(elimFst)               .to[          BorrowedBasket |*| (GoodsSupply |*| CoinSink)  ]
      .>(elimFst(returnBasket)) .to[                              GoodsSupply |*| CoinSink   ]
      .>(elimFst(closeSupply))  .to[                                              CoinSink   ]
      .>(closeCoinSink)         .to[                                              One        ]

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
    id                                           [ Items |*| ( BorrowedBasket |*| (          GoodsSupply   |*| CoinSink) ) ]
      .>(snd(assocRL))                        .to[ Items |*| ((BorrowedBasket |*|            GoodsSupply ) |*| CoinSink  ) ]
      .>(snd(fst(sequence_PN)))               .to[ Items |*| ((BorrowedBasket |*|            GoodsSupply ) |*| CoinSink  ) ] // sequence to prevent picking item before basket is ready
      .>(snd(fst(snd(supplyItem(pick)))))     .to[ Items |*| ((BorrowedBasket |*| (Item  |*| GoodsSupply)) |*| CoinSink  ) ]
      .>(snd(fst(assocRL) > assocLR))         .to[ Items |*| ((BorrowedBasket |*|  Item) |*| (GoodsSupply  |*| CoinSink) ) ]
      .>(snd(fst(swap)))                      .to[ Items |*| ((Item |*|  BorrowedBasket) |*| (GoodsSupply  |*| CoinSink) ) ]
      .>(snd(fst(sequence)))                  .to[ Items |*| ((Item |*|  BorrowedBasket) |*| (GoodsSupply  |*| CoinSink) ) ]
      .>(snd(assocLR))                        .to[ Items |*| (Item  |*| (BorrowedBasket  |*| (GoodsSupply  |*| CoinSink))) ]
      .>(assocRL > fst(swap))                 .to[ (Item |*| Items) |*| (BorrowedBasket  |*| (GoodsSupply  |*| CoinSink))  ]

  private def extractItem[Item: Deferrable.Positive, Items]: Shopping[Item |*| Items] -⚬ (Item |*| Shopping[Items]) =
    IXI > fst(swap > sequence > swap) > IXI > assocLR

  private def ingestCoin[Items]: (Coin |*| Shopping[Items]) -⚬ Shopping[Items] =
    λ { case (coin |*| (items |*| (borrowedBasket |*| (goodsSupply |*| coinSink)))) =>
      // sequence basket after coin to prevent returning basket before purchase is paid
      val (borrowedBasket1 |*| coin1) = borrowedBasket sequenceAfter coin
      val coinSink1 = sendCoin(coin1 |*| coinSink)
      items |*| (borrowedBasket1 |*| (goodsSupply |*| coinSink1))
    }

  private def payForItem[
    Item: SignalingJunction.Positive,
    Items,
  ]: (Coin |*| Shopping[Item |*| Items]) -⚬ (Item |*| Shopping[Items]) =
    id                                         [  Coin |*|  Shopping[Item |*| Items]   ]
      .>.snd(extractItem)                   .to[  Coin |*| (Item  |*| Shopping[Items]) ]
      .>(assocRL)                           .to[ (Coin |*|  Item) |*| Shopping[Items]  ]
      .>(fst(sequence[Coin, Item]))         .to[ (Coin |*|  Item) |*| Shopping[Items]  ] // sequence to prevent using the item before Coin is provided
      .>(fst(swap))                         .to[ (Item |*|  Coin) |*| Shopping[Items]  ]
      .>(assocLR)                           .to[  Item |*| (Coin  |*| Shopping[Items]) ]
      .>.snd(ingestCoin)                    .to[  Item |*|            Shopping[Items]  ]

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
