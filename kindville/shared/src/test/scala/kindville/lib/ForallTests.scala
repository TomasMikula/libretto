package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ForallTests extends AnyFunSuite {
  test("Nil : Forall[List]") {
    val nil: Forall[* :: TNil, List] =
      Forall[* :: TNil, List]([A] => (_: Unit) => List.empty[A])

    val is: List[Int]    = nil.at[Int](())
    val ss: List[String] = nil.at[String](())

    assert(is == Nil)
    assert(ss == Nil)
  }

}
