package libretto.examples

import libretto.StarterApp

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
   * The protocol expresses that:
   *  - The party on the left has to send `"ping"`, receive `"pong"` and send a [[Done]] signal.
   *  - Dually, the party on the right has to receive `"ping"`, send `"pong"` and receive a [[Done]] signal.
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
      .>(constVal("ping"))                 .to [  Val["ping"]                                    ] // (3)
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
    //  (3) When the Done signal from the previous step arrives, replace it with a value of the (singleton) type "ping".
    //  (4) We can always add `One`, which is a neutral element for the concurrent pair `|*|`.
    //  (5) `snd(f)` means we are operating on the second part of a concurrent pair (`|*|`) by `f`.
    //      `promise[A]: One -⚬ (Neg[A] |*| Val[A])` creates, out of nothing (`One`), a demand `Neg[A]`
    //      for a value of type `A`, and a (future) value `Val[A]` of type `A` that gets completed when
    //      the demand is fulfilled. In our case, once the demand for `"pong"` is fulfilled (by a component,
    //      namely Bob, connected to the right of Alice), we obtain a value of type `"pong"`.
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
   */
  override def blueprint: Done -⚬ Done =
    alice > bob
}
