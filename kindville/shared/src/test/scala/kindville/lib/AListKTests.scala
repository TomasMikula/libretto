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

    type Id[A] = A
    val in: App[kindville.*, Id, Int] =
      App.packer[*](504030201)
    val action: Action[kindville.*, Id, Function1] =
      Action.pack[*, Id, Function1]([A, B] => (a: A, f: A => B) => f(a))

    val out1 = AListK.foldLeft[*, Id, Function1, Int, Boolean](in, f, action).unpack
    val out2 = AListK.foldLeft[*, Id, Function1, Int, Boolean](in, g, action).unpack

    assert(out1 == false)
    assert(out2 == false)
  }
}
