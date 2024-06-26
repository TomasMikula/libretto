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

  test("reverse andThen headOption, headOption after reverse") {
    val reverse =
      FunctionK[* :: TNil, List, List](
        [X] => (xs: List[X]) => xs.reverse
      )

    val headOption =
      FunctionK[* :: TNil, List, Option](
        [X] => (xs: List[X]) => xs.headOption
      )

    val go1 = reverse andThen headOption
    val go2 = headOption after reverse

    assert(go1(List(1, 2, 3)) == Some(3))
    assert(go2(List(1, 2, 3)) == Some(3))
    assert(go1(List("1", "2", "3")) == Some("3"))
    assert(go2(List("1", "2", "3")) == Some("3"))
    assert(go1(Nil) == None)
    assert(go2(Nil) == None)
  }

  test("headOption, reverse, created via FunctionK.make[* :: TNil]") {
    val mk = FunctionK.make[* :: TNil]

    // check the inferred type of `mk`
    val _ : [F[_], G[_]] => ([A] => F[A] => G[A]) => FunctionK[* :: TNil, F, G] =
      mk

    val headOption = mk[List, Option]([X] => xs => xs.headOption)
    val reverse    = mk[List, List]  ([X] => xs => xs.reverse)

    assert(headOption(reverse(List(1, 2, 3))) == Some(3))
  }
}
