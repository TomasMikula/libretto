package kindville

import org.scalatest.funsuite.AnyFunSuite

class TypeAppTests extends AnyFunSuite {

  test("inferResult") {
    val ev =
      TypeApp.inferResult[Map, Int :: String :: TNil]

    // proof that the result type Map[Int, String] was inferred
    val ev1: TypeApp[Map, Int :: String :: TNil, Map[Int, String]] =
      ev
  }

}
