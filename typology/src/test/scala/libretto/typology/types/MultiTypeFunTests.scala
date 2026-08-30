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

  private type MTF = MultiTypeFun[TC, _, _]

  private given c: NarrowSymmetricSemigroupalCategory[KindN, MTF, ×] =
    summon

  private val kUnit: KindN[●] = KindN.Type

  private val pairExpr: TypeExpr[TC, ● × ●, ●] =
    TypeExpr.lift(TC.Pair())

  private val pair: MultiTypeFun[TC, ● × ●, ●] =
    MultiTypeFun(pairExpr)

  private val dup: MultiTypeFun[TC, ●, ● × ●] =
    MultiTypeFun.dup

  test("id") {
    c.id(kUnit)
  }

  test("swap") {
    c.swap(kUnit, kUnit)
  }

  test("assocLR and assocRL") {
    c.assocLR(kUnit, kUnit, kUnit)
    c.assocRL(kUnit, kUnit, kUnit)
  }

  test("par") {
    c.par(pair, pair)
  }

  test("derived ix, xi, ixi") {
    c.ix(kUnit, kUnit, kUnit)
    c.xi(kUnit, kUnit, kUnit)
    c.ixi(kUnit, kUnit, kUnit, kUnit)
  }

  test("andThen: dup > pair") {
    val f: MultiTypeFun[TC, ●, ●] = c.andThen(dup, pair)
    f
  }

  test("andThen nesting and par") {
    val h1: MultiTypeFun[TC, ●, ●] = c.andThen(dup, pair)
    val h2: MultiTypeFun[TC, ● × ●, ● × ●] = c.par(h1, h1)
    c.andThen(h2, c.swap(kUnit, kUnit))
  }

  test("composing par and dup") {
    val p_d: MultiTypeFun[TC, ● × ●, (● × ●) × (● × ●)] = c.par(dup, dup)
    c.andThen(p_d, c.par(pair, pair))
  }
}
