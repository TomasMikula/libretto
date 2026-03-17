package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ArrowTests extends AnyFunSuite {

  test("pack/unpack Function1") {
    val x: Arrow[kindville.*, Function1, String, Int] =
      Arrow.pack[*, Function1, String, Int](_.length())

    val y: Arrow[kindville.*, Function1, String, Int] =
      Arrow.packer[*](_.length())

    val f: String => Int =
      Arrow.unpack(x)

    val g: String => Int =
      Arrow.unpack(y)

    assert(f("hello") == 5)
    assert(g("hello") == 5)
  }

}
