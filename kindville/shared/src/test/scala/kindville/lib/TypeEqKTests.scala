package kindville.lib

import kindville.*
import org.scalatest.funsuite.AnyFunSuite

class TypeEqKTests extends AnyFunSuite {

  test("TypeEqK[*, Int, Int]") {
    val ev: TypeEqK[kindville.*, Int, Int] =
      TypeEqK.refl[*][Int](())

    assert(ev.substituteCo[List](List(1, 2, 3)) == List(1, 2, 3))
    assert(ev.substituteCo      (List(1, 2, 3)) == List(1, 2, 3))
  }

  test("TypeEqK[* ->> *, List, List]") {
    case class Foo[F[_]](value: F[Int])

    val ev =
      TypeEqK.refl[* ->> *][List](())

    val ev1: TypeEqK[* ->> *, List, List] =
      ev

    assert(ev.substituteCo[Foo](Foo(List(1, 2, 3))) == Foo(List(1, 2, 3)))
    assert(ev.substituteCo     (Foo(List(1, 2, 3))) == Foo(List(1, 2, 3)))
  }

  test("andThen, flip") {
    case class Foo[F[_]](value: F[Int])

    def andThenFlipped[F[_], G[_], H[_]](
      ev1: TypeEqK[* ->> *, F, G],
      ev2: TypeEqK[* ->> *, H, G],
    ): TypeEqK[* ->> *, F, H] =
      ev1.andThen(ev2.flip)

    val ev = TypeEqK.refl[* ->> *][List](())
    val res = andThenFlipped(ev, ev)
      .substituteCo(Foo(List(1, 2, 3)))

    assert(res == Foo(List(1, 2, 3)))
  }
}
