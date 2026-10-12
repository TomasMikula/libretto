package libretto.typology.types

import libretto.lambda.NarrowSymmetricSemigroupalCategory
import libretto.typology.kinds.*
import org.scalatest.funsuite.AnyFunSuite

class MultiTypeFunLambdaTests extends AnyFunSuite {
  private sealed trait TC[K, L]
  private object TC {
    case object Pair extends TC[● × ●, ●]
    case object IntType extends TC[○, ●]
    case object StringType extends TC[○, ●]
  }

  private val syntax = MultiTypeFun.lambdaSyntax[TC]
  import syntax.*

  private val cat = summon[NarrowSymmetricSemigroupalCategory[KindN, MultiTypeFun[TC, _, _], ×]]
  private val pairExpr: TypeExpr[TC, ● × ●, ●] = TypeExpr.lift(TC.Pair)
  private val pair = MultiTypeFun(pairExpr)
  private val intType: TypeExpr[TC, ○, ●] = TypeExpr.lift(TC.IntType)
  private val stringType: TypeExpr[TC, ○, ●] = TypeExpr.lift(TC.StringType)

  test("identity, swap, duplication, and projection") {
    assert(lambda[●, ●](a => a) == cat.id[●])
    assert(lambda[●, ● × ●](a => a zip a) == MultiTypeFun.dup[TC, ●])
    assert(lambda[● × ●, ● × ●] { ab =>
      val zip(a, b) = ab
      b zip a
    } == cat.swap[●, ●])
    assert(lambda[● × ●, ●](ab => ab.unzip._1) == MultiTypeFun.elimSnd[TC, ●, ●])
    assert(lambda[● × ●, ●](ab => ab.unzip._2) == MultiTypeFun.elimFst[TC, ●, ●])
  }

  test("composite inputs can be duplicated and reassociated") {
    assert(lambda[● × ●, (● × ●) × (● × ●)](ab => ab zip ab) == MultiTypeFun.dup[TC, ● × ●])
    val f = lambda[(● × ●) × ●, ● × (● × ●)] { abc =>
      val zip(zip(a, b), c) = abc
      a zip (b zip c)
    }
    assert(f == cat.assocLR[●, ●, ●])
  }

  test("expressions retain kind witnesses for abstract components") {
    def reverse[K, L](using KindN[K × L]): MultiTypeFun[TC, K × L, L × K] =
      lambda[K × L, L × K] { ab =>
        val (a, b) = ab.unzip
        given KindN[K] = a.kind
        given KindN[L] = b.kind
        cat.id[L](b) zip cat.id[K](a)
      }

    assert(reverse[●, ● × ●] == cat.swap[●, ● × ●])
  }

  test("primitive application with shared input and multiple outputs") {
    val f = lambda[●, ● × ●] { a => pair(a zip a) zip a }
    val expected = MultiTypeFun.dup[TC, ●] > cat.narrowPar(MultiTypeFun.dup[TC, ●] > pair, cat.id[●])
    assert(f == expected)
  }

  test("TypeFun and TypeExpr applications recover their output kinds") {
    val pairFun = TypeFun.fromExpr(pairExpr)
    val f = lambda[● × ●, ●](ab => pairFun(ab))
    val g = lambda[● × ●, ●](ab => pairExpr(ab))
    assert(f == pair)
    assert(g == pair)
  }

  test("parallel primitive applications compose on both sides") {
    val diagonal = MultiTypeFun.dup[TC, ●] > pair
    val both = MultiTypeFun.par(diagonal, diagonal)
    val f = lambda[● × ●, ● × ●] { ab =>
      val (a, b) = both(ab).unzip
      pair(a zip a) zip pair(b zip b)
    }
    assert(f == (both > both))
  }

  test("constants can be combined with inputs on either side") {
    val f = lambda[●, ● × ●] { a => const(intType) zip a }
    val g = lambda[●, ● × ●] { a => a zip const(TypeFun.fromExpr(stringType)) }
    assert(f == MultiTypeFun.introFst[TC, ●, ●](TypeFun.fromExpr(intType)))
    assert(g == MultiTypeFun.introSnd[TC, ●, ●](TypeFun.fromExpr(stringType)))
  }

  test("constant results can discard the entire input") {
    val f = lambda[● × ●, ● × ●] { _ => const(intType) zip const(stringType) }
    val expected = MultiTypeFun.elim[TC, ● × ●] > MultiTypeFun.introBoth(intType, stringType)
    assert(f == expected)
  }

  test("a multi-output constant can be introduced and destructured") {
    val constant = MultiTypeFun.introBoth(intType, stringType)
    val f = lambda[●, ● × ●] { _ =>
      val (i, s) = const(constant).unzip
      s zip i
    }
    assert(f == (MultiTypeFun.elim[TC, ●] > MultiTypeFun.introBoth(stringType, intType)))
  }

  test("projecting partial arguments can keep both, one, or neither input") {
    val addConstants = MultiTypeFun.par(
      MultiTypeFun.introFst[TC, ●, ●](TypeFun.fromExpr(intType)),
      MultiTypeFun.introSnd[TC, ●, ●](TypeFun.fromExpr(stringType)),
    )
    val keepBoth = lambda[● × ●, ● × ●] { ab =>
      val zip(zip(_, a), zip(b, _)) = addConstants(ab)
      a zip b
    }
    val keepFirst = lambda[● × ●, ● × ●] { ab =>
      val zip(zip(_, a), zip(_, s)) = addConstants(ab)
      a zip s
    }
    val keepSecond = lambda[● × ●, ● × ●] { ab =>
      val zip(zip(i, _), zip(b, _)) = addConstants(ab)
      i zip b
    }
    val keepNeither = lambda[● × ●, ● × ●] { ab =>
      val zip(zip(i, _), zip(_, s)) = addConstants(ab)
      i zip s
    }
    assert(keepBoth == cat.id[● × ●])
    assert(keepFirst == (MultiTypeFun.elimSnd[TC, ●, ●] > MultiTypeFun.introSnd[TC, ●, ●](TypeFun.fromExpr(stringType))))
    assert(keepSecond == (MultiTypeFun.elimFst[TC, ●, ●] > MultiTypeFun.introFst[TC, ●, ●](TypeFun.fromExpr(intType))))
    assert(keepNeither == (MultiTypeFun.elim[TC, ● × ●] > MultiTypeFun.introBoth(intType, stringType)))
  }

  test("top-level lambdas report free variables") {
    var escaped: Option[Expr[●]] = None
    lambda[●, ●] { a => escaped = Some(a); a }
    val e = intercept[IllegalArgumentException] {
      lambda[●, ● × ●] { b => escaped.get zip b }
    }
    assert(e.getMessage.contains("Undefined variables"))
    assert(e.getMessage.contains("Lambda parameter"))
  }

  test("lambda inputs and mapped outputs must have non-empty kinds") {
    assertDoesNotCompile("""lambda[○, ○](a => a)""")
    assertDoesNotCompile("""lambda[●, ○](a => MultiTypeFun.elim[TC, ●](a))""")
  }
}
