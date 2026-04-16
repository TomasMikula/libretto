package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class AppTests extends AnyFunSuite {

  test("pack, unpack of Option[Int]") {
    val x1: App[kindville.*, Option, Int] =
      App.pack[kindville.*, Option, Int](Some(1))

    val x2: App[* :: TNil, Option, Int :: TNil] =
      App.pack[* :: TNil, Option, Int :: TNil](Some(1))

    val x3: App[kindville.*, Option, Int] =
      App.packer[kindville.*][Option, Int](Some(1))

    val x4: App[* :: TNil, Option, Int :: TNil] =
      App.packer[* :: TNil][Option, Int](Some(1))

    val y11: Option[Int] = App.unpack(x1)
    val y12: Option[Int] = App.unpacker[*](x1)
    val y21: Option[Int] = App.unpack(x2)
    val y22: Option[Int] = App.unpacker[* :: TNil](x2)
    val y31: Option[Int] = App.unpack(x3)
    val y32: Option[Int] = App.unpacker[*](x3)
    val y41: Option[Int] = App.unpack(x4)
    val y42: Option[Int] = App.unpacker[* :: TNil](x4)

    assert(y11 == Some(1))
    assert(y12 == Some(1))
    assert(y21 == Some(1))
    assert(y22 == Some(1))
    assert(y31 == Some(1))
    assert(y32 == Some(1))
    assert(y41 == Some(1))
    assert(y42 == Some(1))
  }

  test("pack, unpack of Map[String, Int]") {
    val x1: App[* :: * :: TNil, Map, String :: Int :: TNil] =
      App.pack[* :: * :: TNil, Map, String :: Int :: TNil](Map("foo" -> 3))
    val x2: App[* :: * :: TNil, Map, String :: Int :: TNil] =
      App.packer[* :: * :: TNil][Map, String, Int](Map("foo" -> 3))

    val y11: Map[String, Int] = App.unpack(x1)
    val y12: Map[String, Int] = App.unpacker[* :: * :: TNil](x1)
    val y21: Map[String, Int] = App.unpack(x2)
    val y22: Map[String, Int] = App.unpacker[* :: * :: TNil](x2)

    assert(y11 == Map("foo" -> 3))
    assert(y12 == Map("foo" -> 3))
    assert(y21 == Map("foo" -> 3))
    assert(y22 == Map("foo" -> 3))
  }

  test("pack, unpack of MonadError[Either[String, _], String]") {
    import kindville.->

    trait MonadError[F[_], E]

    val monadErrorEitherString: MonadError[Either[String, _], String] =
      new MonadError[Either[String, _], String] {}

    val x1: App[(* -> *) :: * :: TNil, MonadError, Either[String, _] :: String :: TNil] =
      App.pack[(* -> *) :: * :: TNil, MonadError, Either[String, _] :: String :: TNil](monadErrorEitherString)

    val x2: App[(* -> *) :: * :: TNil, MonadError, Either[String, _] :: String :: TNil] =
      App.packer[(* -> *) :: * :: TNil][MonadError, Either[String, _], String](monadErrorEitherString)

    val y11: MonadError[Either[String, _], String] = App.unpack(x1)
    val y12: MonadError[Either[String, _], String] = App.unpacker[(* -> *) :: * :: TNil](x1)
    val y21: MonadError[Either[String, _], String] = App.unpack(x2)
    val y22: MonadError[Either[String, _], String] = App.unpacker[(* -> *) :: * :: TNil](x2)

    assert(y11 == monadErrorEitherString)
    assert(y12 == monadErrorEitherString)
    assert(y21 == monadErrorEitherString)
    assert(y22 == monadErrorEitherString)
  }

}
