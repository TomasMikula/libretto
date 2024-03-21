package kindville.lib

import kindville.*
import kindville.lib.FunctionK.given
import org.scalatest.funsuite.AnyFunSuite

class FunctionKTests extends AnyFunSuite {

  test("headOption") {
    val headOption =
      FunctionK[* :: TNil, List, Option](
        [X] => (xs: List[X]) => xs.headOption
      )

    assert(headOption(List(1, 2, 3)) == Some(1))
    assert(headOption(List("1", "2", "3")) == Some("1"))
    assert(headOption(Nil) == None)
  }

  test("reverse andThen headOption") {
    val reverse =
      FunctionK[* :: TNil, List, List](
        [X] => (xs: List[X]) => xs.reverse
      )

    val headOption =
      FunctionK[* :: TNil, List, Option](
        [X] => (xs: List[X]) => xs.headOption
      )

    val go = reverse andThen headOption

    assert(go(List(1, 2, 3)) == Some(3))
    assert(go(List("1", "2", "3")) == Some("3"))
    assert(go(Nil) == None)
  }
}
