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

    def useToiletPaper: ToiletPaper -⚬ Done =
      id[Done]

    def drinkBeer: Beer -⚬ Done =
      id[Done]

    implicit def signalingJunctionToiletPaper: SignalingJunction.Positive[ToiletPaper] =
      SignalingJunction.Positive.signalingJunctionPositiveDone

    implicit def signalingJunctionBeer: SignalingJunction.Positive[Beer] =
      SignalingJunction.Positive.signalingJunctionPositiveDone
  }

  import goods._

  trait Protocol {
    type Supermarket
    type Shopping[Items]

    implicit def comonoidSupermarket: Comonoid[Supermarket]
    implicit def basketReadiness[Items]: Signaling.Positive[Shopping[Items]]

    def enterAndObtainBasket: Supermarket -⚬ Shopping[One]

    def addBeerToBasket       [Items]: Shopping[Items] -⚬ Shopping[Beer        |*| Items]
    def addToiletPaperToBasket[Items]: Shopping[Items] -⚬ Shopping[ToiletPaper |*| Items]

    def payForBeer       [Items]: (Coin |*| Shopping[Beer        |*| Items]) -⚬ (Beer        |*| Shopping[Items])
    def payForToiletPaper[Items]: (Coin |*| Shopping[ToiletPaper |*| Items]) -⚬ (ToiletPaper |*| Shopping[Items])

    def returnBasketAndLeave: Shopping[One] -⚬ One
  }

  object storekeeper extends Protocol {
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
      Shopping.addItemToBasket(chooseToiletPaper)

    override def addBeerToBasket[Items]: Shopping[Items] -⚬ Shopping[Beer |*| Items] =
      Shopping.addItemToBasket(chooseBeer)

    override def payForToiletPaper[Items]: (Coin |*| Shopping[ToiletPaper |*| Items]) -⚬ (ToiletPaper |*| Shopping[Items]) =
      payForItem[ToiletPaper, Items]

    override def payForBeer[Items]: (Coin |*| Shopping[Beer |*| Items]) -⚬ (Beer |*| Shopping[Items]) =
      payForItem[Beer, Items]

    private def payForItem[
      Item: SignalingJunction.Positive,
      Items,
    ]: (Coin |*| Shopping[Item |*| Items]) -⚬ (Item |*| Shopping[Items]) =
      id                                         [  Coin |*|  Shopping[Item |*| Items]   ]
        .>.snd(Shopping.extractItem)          .to[  Coin |*| (Item  |*| Shopping[Items]) ]
        .>(assocRL)                           .to[ (Coin |*|  Item) |*| Shopping[Items]  ]
        .>(fst(sequence[Coin, Item]))         .to[ (Coin |*|  Item) |*| Shopping[Items]  ] // sequence to prevent using the item before Coin is provided
        .>(fst(swap))                         .to[ (Item |*|  Coin) |*| Shopping[Items]  ]
        .>(assocLR)                           .to[  Item |*| (Coin  |*| Shopping[Items]) ]
        .>.snd(Shopping.ingestCoin)           .to[  Item |*|            Shopping[Items]  ]

    def makeGoodsSupply: Done -⚬ (GoodsSupply |*| Done) = rec { self =>
      Unlimited.createWith[Done, ItemSelection, Done](
        case0 = id[Done],
        case1 = fork > fst(choice(produceBeer, produceToiletPaper)),
        caseN = forkMap(self, self) > IXI > snd(join),
      )
    }

    def coinsToBank: One -⚬ (CoinSink |*| CoinBank) =
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

  private def randomDelay: Done -⚬ Done =
    constVal(()) > mapVal(_ => (scala.util.Random.nextDouble * 1000 + 100).toInt.millis) > delay

  /** Blueprint for customer behavior. A customer has access to a supermarket and runs to completion ([[Done]]). */
  def customer(who: String): Supermarket -⚬ Done = {
    def getCoin: One -⚬ Coin =
      done > printLine(s"🪙 $who is forging a coin") > forgeCoin

    def payForBeerWithForgedMoney[Items]: Shopping[Beer |*| Items] -⚬ (Beer |*| Shopping[Items]) =
      introFst(getCoin) > payForBeer

    def payForToiletPaperWithForgedMoney[Items]: Shopping[ToiletPaper |*| Items] -⚬ (ToiletPaper |*| Shopping[Items]) =
      introFst(getCoin) > payForToiletPaper

    def useTP = delayUsing[ToiletPaper](randomDelay) > useToiletPaper
    def drink = delayUsing[Beer       ](randomDelay) > drinkBeer

    λ { (supermarket: $[Supermarket]) =>
      val ((shopping: $[Shopping[One]]) |*| (basketObtained: $[Done])) =
        enterAndObtainBasket(supermarket) > basketReadiness.signalDone

      val logged: $[Done] =
        when(basketObtained) {
          printLine(s"${Console.RED}+1${Console.RESET} $who obtained a shopping basket")
        }

      val (shopping1 |*| beerAdded) =
        shopping > addBeerToBasket > addBeerToBasket > basketReadiness.signalDone

      val logged1: $[Done] =
        when(join(logged |*| beerAdded)) {
          printLine(s"$who added 2 beers to the basket")
        }

      val (shopping2 |*| tpAdded) =
        shopping1 > addToiletPaperToBasket > basketReadiness.signalDone

      val logged2: $[Done] =
        when(join(logged1 |*| tpAdded)) {
          printLine(s"$who added toilet paper to the basket")
        }

      val (tp |*| shopping3) =
        payForToiletPaperWithForgedMoney(shopping2)

      val (beer1 |*| shopping4) =
        payForBeerWithForgedMoney(shopping3)

      val (beer2 |*| shopping5) =
        payForBeerWithForgedMoney(shopping4)

      val (shopping6 |*| paid) =
        shopping5 > basketReadiness.signalDone

      val logged3: $[Done] =
        when(join(logged2 |*| paid)) {
          printLine(s"$who paid for the purchase")
        }

      val shoppingFinished: $[Done] =
        (returnBasketAndLeave(shopping6) |*| logged3) > elimFst >
          printLine(s"${Console.GREEN}-1${Console.RESET} $who returned the basket")

      val beer1Drunk: $[Done] =
        drink(beer1 waitFor shoppingFinished) > printLine(s"🍺 $who drank the 1st beer")

      val beer2Drunk: $[Done] =
        drink(beer2 waitFor beer1Drunk) > printLine(s"🍺 $who drank the 2nd beer")

      useTP(tp waitFor beer2Drunk) > printLine(s"🧻 $who used the toilet paper")
    }
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
