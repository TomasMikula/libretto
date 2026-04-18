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

  test("pack/unpack BiFunction") {
    case class BiFunction[A1, A2, B1, B2](f: (A1, A2) => (B1, B2)):
      def apply(a1: A1, a2: A2): (B1, B2) = f(a1, a2)

    val x: Arrow[* :: * :: TNil, BiFunction, String :: Int :: TNil, Int :: String :: TNil] =
      Arrow.pack[* :: * :: TNil, BiFunction, String :: Int :: TNil, Int :: String :: TNil](BiFunction((a, b) => (b, a)))

    val y: Arrow[* :: * :: TNil, BiFunction, String :: Int :: TNil, Int :: String :: TNil] =
      Arrow.packer[* :: * :: TNil](BiFunction((a, b) => (b, a)))

    val fx: BiFunction[String, Int, Int, String] = Arrow.unpack(x)
    val fy: BiFunction[String, Int, Int, String] = Arrow.unpack(y)
    val gx: BiFunction[String, Int, Int, String] = Arrow.unpacker[* :: * :: TNil](x)
    val gy: BiFunction[String, Int, Int, String] = Arrow.unpacker[* :: * :: TNil](y)

    assert(fx("hello", 1) == (1, "hello"))
    assert(fy("hello", 1) == (1, "hello"))
    assert(gx("hello", 1) == (1, "hello"))
    assert(gy("hello", 1) == (1, "hello"))
  }

}
