package libretto.examples

import libretto.scaletto.StarterApp

/**
 * This example implements interaction between two parties, Alice and Bob, in which
 *
 *  - Alice sends "ping" to Bob,
 *  - Bob sends "pong" back to Alice,
 *  - Alice sends Done to Bob,
 *
 * in this order, after which no more interaction between the two takes place.
 *
 * This example demonstrates:
 *
 *  - A simple protocol between two parties.
 *  - Linearity: obligation to consume every input exactly once and fulfill every demand exactly once.
 *    Linearity is key to ensuring adherence to a protocol.
 *  - Inverting the flow of values from left-to-right to right-to-left and vice versa.
 */
object PingPong extends StarterApp {
  /**
   * ```
   *          ┃
   *          ┞───────────┐
   *       ┄┄→╎Val["ping"]│┄┄→
   *          ┟───────────┘
   *          ┃
   *          ┞───────────┐
   *       ←┄┄╎Neg["pong"]│←┄┄
   *          ┟───────────┘
   *          ┃
   *          ┞───────────┐
   *       ┄┄→╎   Done    │┄┄→
   *          ┟───────────┘
   *          ┃
   * ```
   *
   *  - `Val[A]` is a value of type `A` traveling left-to-right (the positive direction).
   *  - `Neg[A]` is a value of type `A` traveling right-to-left (the negative direction).
   *    It can be thought of as a _demand_ for `A`, analogous to `Promise[A]` from the Scala library.
   *  - `Done` is a signal traveling left-to-right. It carries no additional information (it is like `Val[Unit]`).
   *
   * The protocol expresses that:
   *  - The party to the left has to send `"ping"`, receive `"pong"` and send a [[Done]] signal.
   *  - Dually, the party to the right has to receive `"ping"`, send `"pong"` and receive a [[Done]] signal.
   *
   * Note: The protocol does not dictate any order in which data flows through the three ports—it may all happen concurently.
   * However, the two interacting parties below are defined in so that the interaction proceeds sequentially top-to-bottom
   * (wrt. the above depiction).
   */
  type Protocol = Val["ping"] |*| Neg["pong"] |*| Done

  /**
   * Alice is on the left side of [[Protocol]].
   *
   * ```
   *   ┏━━━━━━━━━━━━━━━━━┓
   *   ┞──────┐          ┞───────────┐
   *   ╎ Done │┄┄┄┄┄┄┄┄┄→╎Val["ping"]│┄┄→
   *   ┟──────┘          ┟───────────┘
   *   ┃                 ┃
   *   ┃                 ┞───────────┐
   *   ┃    alice    ┌┄←┄╎Neg["pong"]│←┄┄
   *   ┃             ┆   ┟───────────┘
   *   ┃             ┆   ┃
   *   ┃             ┆   ┞───────────┐
   *   ┃             └┄→┄╎   Done    │┄┄→
   *   ┃                 ┟───────────┘
   *   ┗━━━━━━━━━━━━━━━━━┛
   * ```
   *
   * Receives a [[Done]] signal from the left, in response to which it sends a `"ping"` to the right.
   * Concurrently, it receives a `"pong"` from the right, in response to which it sends a [[Done]] signal to the right.
   */
  def alice: Done -⚬ Protocol = {
    id                                     .to [     Done                                        ] // (1)
      .>(aliceSays("sending ping"))        .to [     Done                                        ] // (2)
      .>(constVal["ping"])                 .to [  Val["ping"]                                    ] // (3)
      .>(introSnd)                         .to [  Val["ping"] |*|               One              ] // (4)
      .>(snd(promise["pong"]))             .to [  Val["ping"] |*| (Neg["pong"]  |*| Val["pong"]) ] // (5)
      .>(assocRL)                          .to [ (Val["ping"] |*|  Neg["pong"]) |*| Val["pong"]  ] // (6)
      .>(snd(neglect["pong"]))             .to [ (Val["ping"] |*|  Neg["pong"]) |*|    Done      ] // (7)
      .>(snd(aliceSays("got pong, done"))) .to [ (Val["ping"] |*|  Neg["pong"]) |*|    Done      ] // (8)
                                           .to [                    Protocol                     ] // (9)

    // Notes
    // -----
    //  Given `f: A -⚬ B`, `g: B -⚬ C`, then `f > g` (also written `f.>(g)`) connects the two components serially,
    //  producing a component of type `A -⚬ C`.
    //
    //  (1) The `.to[Done]` has no effect. Given `f: A -⚬ B`, `f.to[B]` is equal to just `f`.
    //      The only purpose of the `.to[B]` extension method is to provide intermediate type annotations
    //      as we build a linear function.
    //  (2) When the Done signal arrives, output "sending ping" as Alice and produce a new `Done` signal.
    //  (3) When the Done signal from the previous step arrives, replace it with the value "ping" (of the singleton type "ping").
    //  (4) We can always add `One`, which is a neutral element for the concurrent pair `|*|`.
    //  (5) `snd(f)` means we are operating on the second part of a concurrent pair (`|*|`) by `f`.
    //      `promise[A]: One -⚬ (Neg[A] |*| Val[A])` creates, out of nothing (`One`), a demand `Neg[A]`
    //      for a value of type `A`, and a (future) value `Val[A]` of type `A` that gets completed when
    //      the demand is fulfilled. In other words, it inverts the flow of `A` from right-to-left (`Neg[A]`)
    //      to left-to-right (`Val[A]`).
    //      In our case, once the demand for `"pong"` is fulfilled (by a component connected to the right of Alice
    //      sending a "pong" value to the left), we obtain a value of type `"pong"` (flowing left-to-right).
    //  (6) `assocRL` reassociates `A |*| (B |*| C)` from right to left, i.e. to `(A |*| B) |*| C`.
    //  (7) We neglect the actual value of type `"pong"` (it has to be `"pong"`, anyway).
    //      The value cannot be completely ignored. It is reduced to a `Done` signal, which still has to be awaited by someone.
    //  (8) When the `Done` signal from the previous step (i.e. the `"pong"` value reduced to a `Done` signal)
    //      arrives, output "got pong, done" and produce a new `Done` signal.
    //  (9) Just a reminder that `Protocol` is just a type alias for `(Val["ping"] |*| Neg["pong"]) |*| Done`.
  }

  private def aliceSays(msg: String): Done -⚬ Done =
    printLine(Console.MAGENTA + s"Alice: $msg" + Console.RESET)

  /**
   * Bob is on the right side of [[Protocol]].
   *
   * ```
   *     ┏━━━━━━━━━━━━━━━━━━━━━┓
   *     ┞───────────┐         ┃
   *  ┄┄→╎Val["ping"]│┄→┄┐     ┃
   *     ┟───────────┘   ┆     ┃
   *     ┃               ┆     ┃
   *     ┞───────────┐   ┆     ┃
   *  ←┄┄╎Neg["pong"]│┄←┄┘     ┃
   *     ┟───────────┘         ┃
   *     ┃              bob    ┃
   *     ┞───────────┐         ┞──────┐
   *  ┄┄→╎   Done    │┄┄┄┄┄┄┄┄→╎ Done │
   *     ┟───────────┘         ┟──────┘
   *     ┗━━━━━━━━━━━━━━━━━━━━━┛
   * ```
   *
   * Receives a `"ping"` from the left, in response to which it sends a `"pong"` to the left.
   * Concurrently, it receives a [[Done]] signal from the left and forwards it to the right.
   */
  def bob: Protocol -⚬ Done = {
    val pingToPong: Val["ping"] -⚬ Val["pong"] =
      neglect["ping"] > bobSays("got ping, sending pong") > constVal("pong")

    id                         .to [                   Protocol             ]
                               .to [ (Val["ping"] |*| Neg["pong"]) |*| Done ] // (1)
      .>(fst(fst(pingToPong))) .to [ (Val["pong"] |*| Neg["pong"]) |*| Done ] // (2)
      .>(fst(fulfill["pong"])) .to [              One              |*| Done ] // (3)
      .>(elimFst)              .to [                                   Done ] // (4)
      .>(bobSays("done"))      .to [                                   Done ] // (5)

    // Notes
    // -----
    //  (1) Just a reminder what `Protocol` is a type alias for.
    //  (2) `fst(fst(f))` means we are operating on the first part of the first part of `(A |*| B) |*| C`.
    //      Here, we operate on `Val["ping"]` and transform it into `Val["pong"]` by `pingToPong`.
    //  (3) If (once) we have a value `Val[A]` of type `A`, we can use it to fulfill a demand `Neg[A]`
    //      for a value of type `A` using `fulfill[A]: (Val[A] |*| Neg[A]) -⚬ One`.
    //      In other words, `fulfill` inverts an `A` flowing left-to-right (`Val[A]`) into an `A`
    //      flowing right-to-left (`Neg[A]`). `fulfill` is dual to `promise` seen above.
    //  (4) We can always remove `One`, which is a neutral element for the concurrent pair `|*|`.
    //  (5) Once the `Done` signal arrives from the component to the left of Bob (namely Alice) arrives,
    //      output "done" and produce a new `Done` signal.
  }

  private def bobSays(msg: String): Done -⚬ Done =
    printLine(Console.GREEN + s"Bob:   $msg" + Console.RESET)

  /**
   * Connects [[alice]] and [[bob]], resulting in
   *
   * ```
   *   ┏━━━━━━━━━━━━━━━━━┳━━━━━━━━━━━━━━━━━━━━━┓
   *   ┞──────┐          ┞───────────┐         ┃
   *   ╎ Done │┄┄┄┄┄┄┄┄┄→╎Val["ping"]│┄→┄┐     ┃
   *   ┟──────┘          ┟───────────┘   ┆     ┃
   *   ┃                 ┃               ┆     ┃
   *   ┃                 ┞───────────┐   ┆     ┃
   *   ┃    alice    ┌┄←┄╎Neg["pong"]│┄←┄┘     ┃
   *   ┃             ┆   ┟───────────┘         ┃
   *   ┃             ┆   ┃              bob    ┃
   *   ┃             ┆   ┞───────────┐         ┞──────┐
   *   ┃             └┄→┄╎   Done    │┄┄┄┄┄┄┄┄→╎ Done │
   *   ┃                 ┟───────────┘         ┟──────┘
   *   ┗━━━━━━━━━━━━━━━━━┻━━━━━━━━━━━━━━━━━━━━━┛
   * ```
   *
   * This effectively sequences the whole interaction.
   *
   * The resulting shape is `Done -⚬ Done`. Thanks to linearity, the whole diagram is well-wired.
   * It is impossible to construct a component that has unconnected or multiply-connected ports _inside_.
   * All unconnected ports are on the outside, part of the component's interface.
   */
  override def blueprint: Done -⚬ Done =
    alice > bob
}
