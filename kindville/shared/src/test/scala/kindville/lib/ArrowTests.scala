package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ArrowTests extends AnyFunSuite {

  test("pack/unpack Function1") {
    val x: Arrow[* :: TNil, Function1, String :: TNil, Int :: TNil] =
      Arrow.pack[* :: TNil, Function1, String :: TNil, Int :: TNil](_.length())

    val f: String => Int =
      Arrow.unpack(x)

    assert(f("hello") == 5)
  }

}
