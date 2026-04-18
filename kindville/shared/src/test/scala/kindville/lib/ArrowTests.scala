package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ArrowTests extends AnyFunSuite {

  test("pack/unpack Function1") {
    val x: Arrow[kindville.*, Function1, String, Int] =
      Arrow.pack[*, Function1, String, Int](_.length())

    val y: Arrow[kindville.*, Function1, String, Int] =
      Arrow.packer[*](_.length())

    val fx: String => Int = Arrow.unpack(x)
    val fy: String => Int = Arrow.unpack(y)
    val gx: String => Int = Arrow.unpacker[*](x)
    val gy: String => Int = Arrow.unpacker[*](y)

    assert(fx("hello") == 5)
    assert(fy("hello") == 5)
    assert(gx("hello") == 5)
    assert(gy("hello") == 5)
  }

}
