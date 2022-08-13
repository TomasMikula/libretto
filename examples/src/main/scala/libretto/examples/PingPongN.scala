package libretto.examples

import libretto.scaletto.StarterApp
import scala.concurrent.duration._

/**
 * This example implements interaction between two parties, Alice and Bob, in which
 *
 *  - when it's Alice's turn, she can choose to send "ping" to Bob or to quit;
 *  - when it's Bob's turn, he can choose to send "pong" back to Alice, or to quit;
 *  - interaction continues until one of the parties quits.
 *
 * This is an extension of the [[PingPong]] example to multiple rounds of ping-pong.
 * It further demonstrates:
 *
 *  - The choice operators [[|+|]] and [[|+|]].
 *  - Recursive protocol type.
 */
object PingPongN extends StarterApp { app =>
  type PlayF[Play] =
    (Val["ping"] |*| ((Neg["pong"] |*| Play) |&| Done)) |+|
    Done

  type Play = Rec[PlayF]

  def alice: Done -⚬ Play = rec { alice =>
    val play: Done -⚬ (Val["ping"] |*| ((Neg["pong"] |*| Play) |&| Done)) = {
      val receivePong: One -⚬ (Neg["pong"] |*| Play) =
        promise["pong"] > snd(neglect > alice)

      aliceSays("ping") > constVal("ping") > introSnd(choice(receivePong, done))
    }

    val quit: Done -⚬ Done =
      aliceSays("quit")

    randomChoice > Bool.switch(
      caseTrue = play > injectL,
      caseFalse = quit > injectR,
    ) > pack[PlayF]
  }

  def bob: Play -⚬ Done = rec { bob =>
    val play: (Done |*| (Neg["pong"] |*| Play)) -⚬ Done =
      fst(bobSays("pong") > constVal("pong")) > assocRL > elimFst(fulfill["pong"]) > bob

    val receivePing: (Val["ping"] |*| ((Neg["pong"] |*| Play) |&| Done)) -⚬ Done =
      fst(neglect > randomChoice) > Bool.switchWithR(
        caseTrue = snd(chooseL) > play,
        caseFalse = snd(chooseR) > fst(bobSays("quit")) > join,
      )

    unpack > either(receivePing, id[Done])
  }

  private def randomChoice: Done -⚬ Bool =
    delay(500.millis) > constVal(()) > mapVal(_ => randomBoolean(0.9)) > liftBoolean

  private def randomBoolean(pTrue: Double): Boolean =
    scala.util.Random.nextDouble() <= pTrue

  private def aliceSays(msg: String): Done -⚬ Done =
    printLine(Console.MAGENTA + s"Alice: $msg" + Console.RESET)

  private def bobSays(msg: String): Done -⚬ Done =
    printLine(Console.GREEN + s"Bob:   $msg" + Console.RESET)

  override def blueprint: Done -⚬ Done =
    alice > bob
}
