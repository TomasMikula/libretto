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
}