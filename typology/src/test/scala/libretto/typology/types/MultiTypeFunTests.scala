package libretto.typology.types

import libretto.lambda.NarrowSymmetricSemigroupalCategory
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
}
