package libretto.examples

import org.scalatest.funsuite.AnyFunSuite

/**
 * Tests that the programs successfully assemble.
 * Important for programs written using lambda syntax, as their
 * linearity is checked at assembly time instead of at compile time.
 */
class AssemblyTests extends AnyFunSuite {
  test("CoffeeMachine") {
    val prg =
      coffeemachine.CoffeeMachine.blueprint
  }

  test("Supermarket") {
    val prg =
      supermarket.Supermarket.blueprint
  }

  test("DiningPhilosophers") {
    val prg =
      diningPhilosophers.DiningPhilosophers.blueprint
  }

  test("DogTreatsFactory") {
    val prg =
      dogTreatsFactory.Main.blueprint
  }

  test("Canteen") {
    val prg =
      canteen.Main.blueprint
  }

  test("SunflowerProcessingFactory") {
    val prg =
      sunflowers.Main.blueprint
  }

  test("LibraryOfAlexandria") {
    val prg =
      libraryOfAlexandria.Main.blueprint
  }

  test("TV") {
    val prg =
      tv.Main.blueprint
  }
}