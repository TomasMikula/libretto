package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class AListKTests extends AnyFunSuite {

  test("list of functions") {
    val f: AListK[kindville.*, Function1, Int, Boolean] =
      (_.toString) ::
      ((_: String).split("0")) ::
      ((_: Array[String]).map(_.length)) ::
      ((_: Array[Int]).exists(_ % 2 == 0)) ::
      AListK.empty[*][Function1, Boolean]()

    // same as f, but using AListK.single as a starting point
    val g: AListK[kindville.*, Function1, Int, Boolean] =
      (_.toString) ::
      ((_: String).split("0")) ::
      ((_: Array[String]).map(_.length)) ::
      AListK.single[*]((_: Array[Int]).exists(_ % 2 == 0))
  }
}
