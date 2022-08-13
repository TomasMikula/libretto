package libretto

import libretto.Semigroupoid
import libretto.lambda.Shuffle
import libretto.util.BiInjective
import org.scalatest.funsuite.AnyFunSuite

class ShuffleTests extends AnyFunSuite {
  private val shuffle = new Shuffle[Tuple2]
  import shuffle.~⚬
  import ~⚬.{assocLR, assocRL, fst, id, ix, ixi, par, snd, swap, xi}

  given BiInjective[Tuple2] = new BiInjective[Tuple2] {
    override def unapply[A, B, X, Y](ev: (A, B) =:= (X, Y)): (A =:= X, B =:= Y) =
      (ev.asInstanceOf[A =:= X], ev.asInstanceOf[B =:= Y])
  }

  test("normalization: fst(snd(f)) > assocLR = assocLR > snd(fst(f))") {
    val f: (Int, Char) ~⚬ (Char, Int) = swap

    val s1 = fst(snd(f)) > assocLR
    val s2 = assocLR > snd(fst(f))

    assert(s1 == s2)
  }

  test("normalization: ix = assocLR > snd(swap) > assocRL") {
    assert(ix == assocLR > snd(swap) > assocRL)
  }

  test("normalization: xi = assocRL > fst(swap) > assocLR") {
    assert(xi == assocRL > fst(swap) > assocLR)
  }

  test("normalization: ixi = assocLR > snd(assocRL > fst(swap) > assocLR) > assocRL") {
    assert(ixi == assocLR > snd(assocRL > fst(swap) > assocLR) > assocRL)
  }

  test("normalization: ixi = assocRL > fst(assocLR > snd(swap) > assocRL) > assocLR") {
    assert(ixi == assocRL > fst(assocLR > snd(swap) > assocRL) > assocLR)
  }

  test("normalization: ixi > par(ixi, ixi) > ixi = par(ixi, ixi) > ixi > par(ixi, ixi)") {
    val f = ixi > par(ixi, ixi) > ixi
    val g = par(ixi, ixi) > ixi > par(ixi, ixi)
    assert(f == g)
  }

  test("normalization: f > f.invert = id, where f = par(ixi, ixi) > ixi > par(ixi, ixi)") {
    val f = par(ixi, ixi) > ixi > par(ixi, ixi)
    assert(f > f.invert == id)
  }
}
