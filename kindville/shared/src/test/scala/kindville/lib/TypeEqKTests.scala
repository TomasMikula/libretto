package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class TypeEqKTests extends AnyFunSuite {

  test("TypeEqK[*, Int, Int]") {
    val ev: TypeEqK[kindville.*, Int, Int] =
      TypeEqK.refl[*][Int]()

    assert(ev.substituteCo[List](List(1, 2, 3)) == List(1, 2, 3))
    assert(ev.substituteCo      (List(1, 2, 3)) == List(1, 2, 3))
  }

  test("TypeEqK[* ->> *, List, List]") {
    case class Foo[F[_]](value: F[Int])

    val ev =
      TypeEqK.refl[* ->> *][List]()

    val ev1: TypeEqK[* ->> *, List, List] =
      ev

    assert(ev.substituteCo[Foo](Foo(List(1, 2, 3))) == Foo(List(1, 2, 3)))
    assert(ev.substituteCo     (Foo(List(1, 2, 3))) == Foo(List(1, 2, 3)))
  }

  test("TypeEqK[* :: * :: TNil, Int :: String :: TNil, Int :: String :: TNil]") {
    val ev: TypeEqK[* :: * :: TNil, Int :: String :: TNil, Int :: String :: TNil] =
      TypeEqK.refl[* :: * :: TNil][Int, String]()

    val m = Map(1 -> "foo")

    assert(ev.substituteCo[Map](m) == m)

    def andThenFlipped[A1, A2, B1, B2, C1, C2](
      ev1: TypeEqK[* :: * :: TNil, A1 :: A2 :: TNil, B1 :: B2 :: TNil],
      ev2: TypeEqK[* :: * :: TNil, C1 :: C2 :: TNil, B1 :: B2 :: TNil],
    ): TypeEqK[* :: * :: TNil, A1 :: A2 :: TNil, C1 :: C2 :: TNil] =
      ev1.andThen(ev2.flip)

    val ev1 = andThenFlipped(ev, ev)

    assert(ev1.substituteCo[Map](m) == m)

    val ma: App[* :: * :: TNil, Map, Int :: String :: TNil] =
      App.packer[* :: * :: TNil](m)

    assert(ev1.substituteCoApp(ma).unpack == m)
  }

  test("andThen, flip with higher-kinded type argument") {
    case class Foo[F[_]](value: F[Int])

    def andThenFlipped[F[_], G[_], H[_]](
      ev1: TypeEqK[* ->> *, F, G],
      ev2: TypeEqK[* ->> *, H, G],
    ): TypeEqK[* ->> *, F, H] =
      ev1.andThen(ev2.flip)

    val ev = TypeEqK.refl[* ->> *][List]()
    val res = andThenFlipped(ev, ev)
      .substituteCo(Foo(List(1, 2, 3)))

    assert(res == Foo(List(1, 2, 3)))
  }
}
