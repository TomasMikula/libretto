package libretto

import libretto.impl.{Semigroupoid, Shuffle}
import org.scalatest.funsuite.AnyFunSuite

class ShuffleTests extends AnyFunSuite {
  private val shuffle = new Shuffle[Tuple2]
  import shuffle.~⚬
  import ~⚬.{assocLR, fst, snd}

  given BiInjective[Tuple2] = new BiInjective[Tuple2] {
    override def unapply[A, B, X, Y](ev: (A, B) =:= (X, Y)): (A =:= X, B =:= Y) =
      (ev.asInstanceOf, ev.asInstanceOf)
  }

  test("normalization: fst(snd(f)) > assocLR = assocLR > snd(fst(f))") {
    val f: (Int, Char) ~⚬ (Char, Int) = ~⚬.swap

    val s1 = fst(snd(f)) > assocLR
    val s2 = assocLR > snd(fst(f))

    assert(s1 == s2)
  }
}
