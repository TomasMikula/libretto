package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class ArrowTests extends AnyFunSuite {

  test("pack/unpack Function1") {
    val x: Arrow[kindville.*, Function1, String, Int] =
      Arrow.pack[*, Function1, String, Int](_.length())

    val y: Arrow[kindville.*, Function1, String, Int] =
      Arrow.packer[*](_.length())

    val fx: String => Int = x.unpack
    val fy: String => Int = y.unpack
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

    val fx: BiFunction[String, Int, Int, String] = x.unpack
    val fy: BiFunction[String, Int, Int, String] = y.unpack
    val gx: BiFunction[String, Int, Int, String] = Arrow.unpacker[* :: * :: TNil](x)
    val gy: BiFunction[String, Int, Int, String] = Arrow.unpacker[* :: * :: TNil](y)

    assert(fx("hello", 1) == (1, "hello"))
    assert(fy("hello", 1) == (1, "hello"))
    assert(gx("hello", 1) == (1, "hello"))
    assert(gy("hello", 1) == (1, "hello"))
  }

  test("pack/unpack multiple higher-kinded type parameters") {
    class MyArrowType[
      A, B[_], C[_[_, _], _],
      X, Y[_], Z[_[_, _], _],
    ]

    type Foo[F[_, _], T] = F[T, T]

    val in: MyArrowType[String, List, Foo, Int, Option, Foo] =
      MyArrowType[String, List, Foo, Int, Option, Foo]

    val x: Arrow[
      * :: (* -> *) :: ((((* :: * :: TNil) ->> *) :: * :: TNil) ->> *) :: TNil,
      MyArrowType,
      String :: List   :: Foo :: TNil,
      Int    :: Option :: Foo :: TNil,
    ] =
      Arrow.pack[
        * :: (* -> *) :: ((((* :: * :: TNil) ->> *) :: * :: TNil) ->> *) :: TNil,
        MyArrowType,
        String :: List   :: Foo :: TNil,
        Int    :: Option :: Foo :: TNil,
      ](in)

    val y: Arrow[
      * :: (* -> *) :: ((((* :: * :: TNil) ->> *) :: * :: TNil) ->> *) :: TNil,
      MyArrowType,
      String :: List   :: Foo :: TNil,
      Int    :: Option :: Foo :: TNil,
    ] =
      Arrow.packer[* :: (* -> *) :: ((((* :: * :: TNil) ->> *) :: * :: TNil) ->> *) :: TNil](in)

    val outx1 = x.unpack
    val outx2 = Arrow.unpacker[* :: (* -> *) :: ((((* :: * :: TNil) ->> *) :: * :: TNil) ->> *) :: TNil](x)
    val outy1 = y.unpack
    val outy2 = Arrow.unpacker[* :: (* -> *) :: ((((* :: * :: TNil) ->> *) :: * :: TNil) ->> *) :: TNil](y)

    assert(outx1 == in)
    assert(outx2 == in)
    assert(outy1 == in)
    assert(outy2 == in)
  }

}
