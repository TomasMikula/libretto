package libretto.examples.supermarket

import libretto.scaletto.StarterApp

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
 *    - obligation to return a basket enforced before execution
 *    - the type `Shopping` is a protocol between the store and the customer
 */
object Supermarket extends StarterApp {
  import money.CoinBank
  import SupermarketProvider.Supermarket

  override def blueprint: Done -⚬ Done =
    λ { (start: $[Done]) =>
      val (supermarket |*| coinBank) =
        SupermarketProvider.openSupermarket(capacity = 3)(start)

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

  /** Blueprints for customer behaviors. */
  private def customers: List[Supermarket -⚬ Done] = {
    val customers =
      new Customers(SupermarketProvider)

    List(
      customers.behavior("Alice"),
      customers.behavior("Bryan"),
      customers.behavior("Chloe"),
      customers.behavior("David"),
      customers.behavior("Ellen"),
      customers.behavior("Frank"),
      customers.behavior("Gregg"),
      customers.behavior("Helen"),
      customers.behavior("Isaac"),
      customers.behavior("Julia"),
    )
  }
}
