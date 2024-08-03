package libretto.examples.coffeemachine

import libretto.scaletto.StarterKit.*
import scala.concurrent.duration.*

/**
 * A front panel of a coffee machine. Displays the menu and prompts the user for choices.
 */
object CoffeeMachineClient {
  import Protocol.*

  val useCoffeeMachine: CoffeeMachine -⚬ Done = {
    def go: (Done |*| CoffeeMachine) -⚬ Done = rec { repeat =>
      mainMenu > either(
        fst(serve) > repeat,
        id,
      )
    }

    introFst(done) > go
  }

  private def mainMenu: (Done |*| CoffeeMachine) -⚬ ((Val[Beverage] |*| CoffeeMachine) |+| Done) = {
    type Item = (Done |+| Done) |+| Done
    object Item {
      // constructors
      def espresso: Done -⚬ Item = injectL > injectL
      def latte:    Done -⚬ Item = injectR > injectL
      def quit:     Done -⚬ Item = injectR

      // destructor
      def switchWithR[A, R](
        caseEspresso: (Done |*| A) -⚬ R,
        caseLatte:    (Done |*| A) -⚬ R,
        caseQuit:     (Done |*| A) -⚬ R,
      ): (Item |*| A) -⚬ R =
        distributeR > either(
          distributeR > either(
            caseEspresso,
            caseLatte,
          ),
          caseQuit,
        )
    }

    val msg =
      """Choose your beverage:
        | e - espresso
        | l - latte
        | q - quit
        |""".stripMargin

    val dict = List(
      "e" -> Item.espresso,
      "l" -> Item.latte,
      "q" -> Item.quit,
    )

    λ { case (trigger |*| machine) =>
      val item: $[Item] = trigger > prompt(msg, dict)
      (item |*| machine) > Item.switchWithR(
        caseEspresso = getEspresso > injectL,
        caseLatte    = getLatte    > injectL,
        caseQuit     = quit        > injectR,
      )
    }
  }

  private def getEspresso: (Done |*| CoffeeMachine) -⚬ (Val[Beverage] |*| CoffeeMachine) =
    λ { case (trigger |*| machine) =>
      CoffeeMachine.chooseEspresso(machine).apply(promptShot(trigger))
    }

  private def getLatte: (Done |*| CoffeeMachine) -⚬ (Val[Beverage] |*| CoffeeMachine) =
    λ { case (trigger |*| machine) =>
      CoffeeMachine.chooseLatte(machine).apply(promptLatteOptions(trigger))
    }

  private def quit: (Done |*| CoffeeMachine) -⚬ Done =
    λ { case (trigger |*| machine) =>
      (trigger |*| CoffeeMachine.chooseQuit(machine)) > join
    }

  private def promptLatteOptions: Done -⚬ LatteOptions =
    λ { (trigger: $[Done]) =>
      val (size      |*| sizeDone)  = when(trigger)   { promptSize > signalDone }
      val (shotCount |*| shotsDone) = when(sizeDone)  { promptShot > signalDone }
      val flavor                    = when(shotsDone) { promptFlavor }

      size |*| shotCount |*| flavor
    }

  private def promptShot: Done -⚬ Val[ShotCount] = {
    val msg =
      """Choose strength:
        | s - single espresso shot
        | d - double espresso shot
        |""".stripMargin

    val parse: String => Option[ShotCount] = {
      case "s" => Some(ShotCount.Single)
      case "d" => Some(ShotCount.Double)
      case _   => None
    }

    prompt(msg, parse)
  }

  private def promptSize: Done -⚬ Val[Size] = {
    val msg =
      """Choose your size:
        | s - small
        | m - medium
        | l - large
        |""".stripMargin

    val parse: String => Option[Size] = {
      case "s" => Some(Size.Small)
      case "m" => Some(Size.Medium)
      case "l" => Some(Size.Large)
      case _   => None
    }

    prompt(msg, parse)
  }

  private def promptFlavor: Done -⚬ Val[Option[Flavor]] = {
    val msg =
      """Do you want to add extra flavor to your latte?
        | v - vanilla
        | c - cinnamon
        | n - no extra flavor
        |""".stripMargin

    val parse: String => Option[Option[Flavor]] = {
      case "v" => Some(Some(Flavor.Vanilla))
      case "c" => Some(Some(Flavor.Cinnamon))
      case "n" => Some(None)
      case _   => None
    }

    prompt(msg, parse)
  }

  private def prompt[A](msg: String, parse: String => Option[A]): Done -⚬ Val[A] =
    prompt(msg, mapVal(parse) > optionToPMaybe)

  private def prompt[A](msg: String, dictionary: List[(String, Done -⚬ A)]): Done -⚬ A =
    prompt(msg, Val.switch(dictionary))

  private def prompt[A](msg: String, parse: Val[String] -⚬ PMaybe[A]): Done -⚬ A =
    rec { tryAgain =>
      printLine(msg)
        > readLine
        > parse
        > PMaybe.switch(tryAgain, id)
    }

  private def serve: Val[Beverage] -⚬ Done = {
    val dot: Done -⚬ Done = putStr(".") > delay(500.millis)
    val etc: Done -⚬ Done = dot > dot > dot > printLine("")

    delayVal(etc)
      > mapVal((b: Beverage) => s"☕ Here goes your ${b.description}.")
      > printLine
      > etc
      > printLine("")
  }
}
