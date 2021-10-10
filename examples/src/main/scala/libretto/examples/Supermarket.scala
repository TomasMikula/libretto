package libretto.examples

import libretto.StarterApp
import scala.concurrent.duration._

/**
 * In a pandemic, supermarkets are required to limit the number of customers in the store.
 * A way to achieve it is to provide a limited number of shopping baskets and require that
 * each customer entering the store has a shopping basket. When there are no more baskets,
 * an incoming customer has to wait for a previous customer to leave (and return their basket).
 *
 * This example demonstrates:
 *  - concurrency
 *    - customers come and shop concurrently
 *  - sequencing
 *    - a customer can shop only _after_ obtaining a basket
 *    - a customer can use an item only _after_ paying for it
 *    - ...
 *  - mutual exclusion
 *    - limited number of concurrently shopping customers
 *      - without side-effects on shared synchronization objects (such as semaphores)
 *  - linear & session types
 *    - obligation to return a basket enforced by the type-system
 *    - the type `Shopping` is a protocol between the store and the customer
 */
object Supermarket extends StarterApp {
  import $._
  import money._
  import storekeeper._

  override def blueprint: Done -⚬ Done =
    λ { (start: $[Done]) =>
      val (supermarket |*| coinBank) = storekeeper.openSupermarket(capacity = 3)(start)

      // The Supermarket type is just an *interface* to a supermarket. As such, it can be
      // shared arbitrarily (it is indeed a comonoid), and thus can serve any number of customers.
      val accessSupermarketByCustomers: Supermarket -⚬ LList[Done] =
        LList.fromList(customers)

      val customerHandles: $[LList[Done]] =
        accessSupermarketByCustomers(supermarket)

      // await all customers
      // (`Done` signal is a monoid, so a list of `Done` can be combined into a single `Done`)
      val customersDone: $[Done] =
        customerHandles > LList.fold

      // wait for all customers to finish shopping before opening the coin bank
      val finalCoinBank: $[CoinBank] =
        coinBank waitFor customersDone

      val revenue: $[Val[Int]] =
        money.openCoinBank(finalCoinBank)

      revenue > printLine(n => s"Made $n coins")
    }

  object money {
    opaque type Coin = Done
    opaque type CoinBank = Val[Int] // number of coins

    def forgeCoin(who: String): Done -⚬ Coin =
      printLine(s"🪙 $who is forging a coin")

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

  import baskets._

  object goods {
    // Our supermarket specializes on the most wanted items in a pandemic,
    // namely toilet paper and beer.
    opaque type ToiletPaper = Done
    opaque type Beer = Done

    def produceToiletPaper: Done -⚬ ToiletPaper =
      id[Done]

    def produceBeer: Done -⚬ Beer =
      id[Done]

    def useToiletPaper(who: String): ToiletPaper -⚬ Done =
      printLine(s"🧻 $who is using toilet paper")

    def drinkBeer(who: String): Beer -⚬ Done =
      printLine(s"🍺 $who is drinking beer")

    implicit def signalingJunctionToiletPaper: SignalingJunction.Positive[ToiletPaper] =
      SignalingJunction.Positive.signalingJunctionPositiveDone

    implicit def signalingJunctionBeer: SignalingJunction.Positive[Beer] =
      SignalingJunction.Positive.signalingJunctionPositiveDone
  }

  import goods._

  object storekeeper {
    private type BorrowedBasket = Basket |*| -[Basket]
    private type ItemSelection = Beer |&| ToiletPaper
    private type GoodsSupply = Unlimited[ItemSelection]
    private type CoinSink = Unlimited[-[Coin]]

    opaque type Shopping[ItemsInBasket] =
      ItemsInBasket |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink))

    opaque type Supermarket = Unlimited[Shopping[One]]

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

    private object Shopping {
      def addItemToBasket[Item: SignalingJunction.Positive, Items](
        who: String,
        itemName: String,
        pick: ItemSelection -⚬ Item,
      ): Shopping[Items] -⚬ Shopping[Item |*| Items] = {
        val log: Item -⚬ Item =
          alsoPrintLine[Item](s"$who is adding $itemName to the basket")

        id                                           [ Items |*| ( BorrowedBasket |*| (          GoodsSupply   |*| CoinSink) ) ]
          .>(snd(assocRL))                        .to[ Items |*| ((BorrowedBasket |*|            GoodsSupply ) |*| CoinSink  ) ]
          .>(snd(fst(sequence_PN)))               .to[ Items |*| ((BorrowedBasket |*|            GoodsSupply ) |*| CoinSink  ) ]
          .>(snd(fst(snd(supplyItem(pick)))))     .to[ Items |*| ((BorrowedBasket |*| (Item  |*| GoodsSupply)) |*| CoinSink  ) ]
          .>(snd(fst(assocRL) > assocLR))         .to[ Items |*| ((BorrowedBasket |*|  Item) |*| (GoodsSupply  |*| CoinSink) ) ]
          .>(snd(fst(snd(log) > swap)))           .to[ Items |*| ((Item |*|  BorrowedBasket) |*| (GoodsSupply  |*| CoinSink) ) ]
          .>(snd(fst(sequence)))                  .to[ Items |*| ((Item |*|  BorrowedBasket) |*| (GoodsSupply  |*| CoinSink) ) ]
          .>(snd(assocLR))                        .to[ Items |*| (Item  |*| (BorrowedBasket  |*| (GoodsSupply  |*| CoinSink))) ]
          .>(assocRL > fst(swap))                 .to[ (Item |*| Items) |*| (BorrowedBasket  |*| (GoodsSupply  |*| CoinSink))  ]
      }

      def extractItem[Item: Deferrable.Positive, Items]: Shopping[Item |*| Items] -⚬ (Item |*| Shopping[Items]) =
        IXI > fst(swap > sequence > swap) > IXI > assocLR

      def ingestCoin[Items]: (Coin |*| Shopping[Items]) -⚬ Shopping[Items] =
        λ { case (coin |*| (items |*| (borrowedBasket |*| (goodsSupply |*| coinSink)))) =>
          // sequence basket after coin to prevent returning basket before purchase is paid
          val (borrowedBasket1 |*| coin1) = borrowedBasket sequenceAfter coin
          val coinSink1 = sendCoin(coin1 |*| coinSink)
          items |*| (borrowedBasket1 |*| (goodsSupply |*| coinSink1))
        }
    }

    implicit def comonoidSupermarket: Comonoid[Supermarket] =
      Unlimited.comonoidUnlimited

    def enterAndObtainBasket(who: String): Supermarket -⚬ Shopping[One] = {
      val log: Basket -⚬ Basket =
        alsoPrintLine(s"$who obtained a shopping basket")

      val delaySupply: (BorrowedBasket |*| GoodsSupply) -⚬ (BorrowedBasket |*| GoodsSupply) =
        fst(swap) > assocLR > snd(sequence_PN[Basket, GoodsSupply]) > assocRL > fst(swap)

      id                             [      Supermarket                                        ]
                                  .to[ Unlimited[Shopping[One]]                                ]
        .>(Unlimited.single)      .to[           Shopping[One]                                 ]
                                  .to[ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
        .>(snd(fst(fst(log))))    .to[ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
        .>(snd(assocRL))          .to[ One |*| ((BorrowedBasket |*| GoodsSupply) |*| CoinSink) ]
        .>(snd(fst(delaySupply))) .to[ One |*| ((BorrowedBasket |*| GoodsSupply) |*| CoinSink) ]
        .>(snd(assocLR))          .to[ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
    }

    def returnBasketAndLeave(who: String): Shopping[One] -⚬ One = {
      val log: Basket -⚬ Basket =
        alsoPrintLine(s"$who returned the basket")

      id                             [ One |*| (BorrowedBasket |*| (GoodsSupply |*| CoinSink)) ]
        .>(elimFst)               .to[          BorrowedBasket |*| (GoodsSupply |*| CoinSink)  ]
        .>(fst(fst(log)))         .to[          BorrowedBasket |*| (GoodsSupply |*| CoinSink)  ]
        .>(elimFst(returnBasket)) .to[                              GoodsSupply |*| CoinSink   ]
        .>(elimFst(closeSupply))  .to[                                              CoinSink   ]
        .>(closeCoinSink)         .to[                                              One        ]
    }

    def addToiletPaperToBasket[Items](who: String): Shopping[Items] -⚬ Shopping[ToiletPaper |*| Items] =
      Shopping.addItemToBasket(who, "toilet paper", chooseToiletPaper)

    def addBeerToBasket[Items](who: String): Shopping[Items] -⚬ Shopping[Beer |*| Items] =
      Shopping.addItemToBasket(who, "beer", chooseBeer)

    def payForToiletPaper[Items](customer: String): (Coin |*| Shopping[ToiletPaper |*| Items]) -⚬ (ToiletPaper |*| Shopping[Items]) =
      payForItem[ToiletPaper, Items](customer, "toilet paper")

    def payForBeer[Items](customer: String): (Coin |*| Shopping[Beer |*| Items]) -⚬ (Beer |*| Shopping[Items]) =
      payForItem[Beer, Items](customer, "beer")

    private def payForItem[
      Item: SignalingJunction.Positive,
      Items,
    ](
      who: String,
      itemName: String,
    ): (Coin |*| Shopping[Item |*| Items]) -⚬ (Item |*| Shopping[Items]) = {
      val log: Item -⚬ Item =
        alsoPrintLine[Item](s"$who paid for $itemName")

      id                                         [  Coin |*|  Shopping[Item |*| Items]   ]
        .>.snd(Shopping.extractItem)          .to[  Coin |*| (Item  |*| Shopping[Items]) ]
        .>(assocRL)                           .to[ (Coin |*|  Item) |*| Shopping[Items]  ]
        .>(fst(sequence[Coin, Item]))         .to[ (Coin |*|  Item) |*| Shopping[Items]  ] // sequence to prevent using the item before Coin is provided
        .>(fst(snd(log)))                     .to[ (Coin |*|  Item) |*| Shopping[Items]  ]
        .>(fst(swap > sequence[Item, Coin]))  .to[ (Item |*|  Coin) |*| Shopping[Items]  ] // sequence to delay the Basket (via Coin in ingestCoin) after the "paid" log message
        .>(assocLR)                           .to[  Item |*| (Coin  |*| Shopping[Items]) ]
        .>.snd(Shopping.ingestCoin)           .to[  Item |*|            Shopping[Items]  ]
    }

    def makeGoodsSupply: Done -⚬ (GoodsSupply |*| Done) = rec { self =>
      Unlimited.createWith[Done, ItemSelection, Done](
        case0 = id[Done],
        case1 = fork > fst(choice(produceBeer, produceToiletPaper)),
        caseN = forkMap(self, self) > IXI > snd(join),
      )
    }

    def coinsToDrawer: One -⚬ (CoinSink |*| CoinBank) =
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
        .>(snd(introSnd(coinsToDrawer))).to[ (Unlimited[BorrowedBasket] |*| LList1[Basket]) |*| ((GoodsSupply |*| Done)  |*|  (CoinSink |*| CoinBank)) ]
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

  private def randomDelay: Done -⚬ Done =
    constVal(()) > mapVal(_ => (scala.util.Random.nextDouble * 100 + 10).toInt.millis) > delay

  /** Blueprint for customer behavior. A customer has access to a supermarket and runs to completion ([[Done]]). */
  def customer(who: String): Supermarket -⚬ Done = {
    def payForBeerWithForgedMoney[Items]: Shopping[Beer |*| Items] -⚬ (Beer |*| Shopping[Items]) =
      introFst(done > forgeCoin(who)) > payForBeer(who)

    def payForToiletPaperWithForgedMoney[Items]: Shopping[ToiletPaper |*| Items] -⚬ (ToiletPaper |*| Shopping[Items]) =
      introFst(done > forgeCoin(who)) > payForToiletPaper(who)

    def useTP = delayUsing[ToiletPaper](randomDelay) > useToiletPaper(who)
    def drink = delayUsing[Beer       ](randomDelay) > drinkBeer(who)

    id                                                   [             Supermarket                             ]
      .>(enterAndObtainBasket(who))                   .to[ Shopping[                                    One  ] ]
      .>(addBeerToBasket(who))                        .to[ Shopping[                           Beer |*| One  ] ]
      .>(addBeerToBasket(who))                        .to[ Shopping[                 Beer |*| (Beer |*| One) ] ]
      .>(addToiletPaperToBasket(who))                 .to[ Shopping[ToiletPaper |*| (Beer |*| (Beer |*| One))] ]
      .>(payForToiletPaperWithForgedMoney)            .to[ ToiletPaper |*| Shopping[ Beer |*| (Beer |*| One) ] ]
      .>.snd(payForBeerWithForgedMoney)               .to[ ToiletPaper |*| (Beer |*| Shopping[ Beer |*| One ]) ]
      .>.snd.snd(payForBeerWithForgedMoney)           .to[ ToiletPaper |*| (Beer |*| (Beer |*| Shopping[One])) ]
      .>.snd.snd(elimSnd(returnBasketAndLeave(who)))  .to[ ToiletPaper |*| (Beer |*|  Beer                   ) ]
      .>(par(useTP, (par(drink, drink))))             .to[    Done     |*| (Done |*|  Done                   ) ]
      .>(joinMap(id, join))                           .to[             Done                                    ]
  }

  /** Blueprints for customer behaviors. */
  private def customers: List[Supermarket -⚬ Done] =
    List(
      customer("Alice"),
      customer("Bryan"),
      customer("Chloe"),
      customer("David"),
      customer("Ellen"),
      customer("Frank"),
      customer("Gregg"),
      customer("Helen"),
      customer("Isaac"),
      customer("Julia"),
    )
}
