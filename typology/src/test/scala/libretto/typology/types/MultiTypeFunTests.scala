package libretto.typology.types

import libretto.lambda.NarrowSymmetricSemigroupalCategory
import libretto.lambda.NarrowSymmetricWSemigroupalCategory
import libretto.lambda.NarrowWSemigroupalCategory.\
import libretto.typology.kinds.*
import org.scalatest.funsuite.AnyFunSuite

class MultiTypeFunTests extends AnyFunSuite {

  /** Minimal type constructor, sufficient for these tests. */
  private sealed trait TC[K, L](using
    val inKind: Kinds[K],
    val outKind: Kind[L],
  )

  private object TC {
    case class Pair() extends TC[● × ●, ●]
  }

  private val c: NarrowSymmetricSemigroupalCategory[KindN, MultiTypeFun[TC, _, _], ×] =
    summon

  private val wc: NarrowSymmetricWSemigroupalCategory[Kinds, MultiTypeFun[TC, _, _], Kinds.Prod] =
    summon

  private val pairExpr: TypeExpr[TC, ● × ●, ●] =
    TypeExpr.lift(TC.Pair())

  private val pair: MultiTypeFun[TC, ● × ●, ●] =
    MultiTypeFun(pairExpr)

  private val dup: MultiTypeFun[TC, ●, ● × ●] =
    MultiTypeFun.dup

  test("id") {
    c.id[●]
  }

  test("swap") {
    c.swap[●, ●]
  }

  test("assocLR and assocRL") {
    c.assocLR[●, ●, ●]
    c.assocRL[●, ●, ●]
  }

  test("par") {
    c.narrowPar(pair, pair)
  }

  test("derived ix, xi, ixi") {
    c.ix[●, ●, ●]
    c.xi[●, ●, ●]
    c.ixi[●, ●, ●, ●]
  }

  test("andThen: dup > pair") {
    val f: MultiTypeFun[TC, ●, ●] = c.andThen(dup, pair)
    f
  }

  test("andThen nesting and par") {
    val h1: MultiTypeFun[TC, ●, ●] = c.andThen(dup, pair)
    val h2: MultiTypeFun[TC, ● × ●, ● × ●] = c.narrowPar(h1, h1)
    c.andThen(h2, c.swap[●, ●])
  }

  test("composing par and dup") {
    val p_d: MultiTypeFun[TC, ● × ●, (● × ●) × (● × ●)] = c.narrowPar(dup, dup)
    c.andThen(p_d, c.narrowPar(pair, pair))
  }

  test("intensional iid, iswap, iassocLR, iassocRL") {
    assert((wc.iid[\[●]].underlying: Any) == (c.id[●]: Any))
    assert((wc.iswap[\[●], \[●]].underlying: Any) == (c.swap[●, ●]: Any))
    assert((wc.iassocLR[\[●], \[●], \[●]].underlying: Any) == (c.assocLR[●, ●, ●]: Any))
    assert((wc.iassocRL[\[●], \[●], \[●]].underlying: Any) == (c.assocRL[●, ●, ●]: Any))
  }

  test("intensional ipar") {
    val f1 = wc.`-×>`.lift(c.id[●])
    val f2 = wc.`-×>`.lift(c.id[●])
    assert((wc.ipar(f1, f2).underlying: Any) == (c.narrowPar(c.id[●], c.id[●]): Any))
  }
}
