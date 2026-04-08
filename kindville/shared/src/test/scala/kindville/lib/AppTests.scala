package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class AppTests extends AnyFunSuite {

  test("pack, unpack of Option[Int]") {
    val x1: App[kindville.*, Option, Int] =
      App.pack[kindville.*, Option, Int](Some(1))

    val x2: App[* :: TNil, Option, Int :: TNil] =
      App.pack[* :: TNil, Option, Int :: TNil](Some(1))

    val y1: Option[Int] =
      App.unpack(x1)

    val y2: Option[Int] =
      App.unpack(x2)

    assert(y1 == Some(1))
    assert(y2 == Some(1))
  }

  test("pack, unpack of Map[String, Int]") {
    val x: App[* :: * :: TNil, Map, String :: Int :: TNil] =
      App.pack[* :: * :: TNil, Map, String :: Int :: TNil](Map("foo" -> 3))

    val y: Map[String, Int] =
      App.unpack(x)

    assert(y == Map("foo" -> 3))
  }

}
