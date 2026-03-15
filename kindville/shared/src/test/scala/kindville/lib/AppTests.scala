package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class AppTests extends AnyFunSuite {

  test("pack, unpack") {
    val x: App[* :: TNil, Option, Int :: TNil] =
      App.pack[* :: TNil, Option, Int :: TNil](Some(1))

    val y: Option[Int] =
      App.unpack(x)

    assert(y == Some(1))
  }

}
