package kindville

import org.scalatest.funsuite.AnyFunSuite

class TypeEqTests extends AnyFunSuite {

  test("substituteCo") {
    def go[M[_ <: AnyKind], F <: AnyKind, G <: AnyKind](ev: =~=[F, G])(mf: M[F]): M[G] =
      ev.substituteCo(mf)

    case class Moo[F <: AnyKind]()

    val in = Moo[Option]()
    val out = go[Moo, Option, Option](summon[=~=[Option, Option]])(in)
    assert(out == in)
  }

}
