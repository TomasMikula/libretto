package libretto.typology.types

import libretto.lambda.NarrowSymmetricSemigroupalCategory
import libretto.typology.kinds.*
import org.scalatest.funsuite.AnyFunSuite

class TypeFunLambdaTests extends AnyFunSuite {
  private sealed trait TC[K, L]
  private object TC {
    case object Pair extends TC[● × ●, ●]
    case object IntType extends TC[○, ●]
    case object StringType extends TC[○, ●]
  }

  private val syntax = TypeFun.lambdaSyntax[TC]
  import syntax.*

  private val cat = summon[NarrowSymmetricSemigroupalCategory[KindN, MultiTypeFun[TC, _, _], ×]]
  private val pairExpr: TypeExpr[TC, ● × ●, ●] = TypeExpr.lift(TC.Pair)
  private val pair: TypeFun[TC, ● × ●, ●] = TypeFun.fromExpr(pairExpr)
  private val intType: TypeExpr[TC, ○, ●] = TypeExpr.lift(TC.IntType)
  private val stringType: TypeExpr[TC, ○, ●] = TypeExpr.lift(TC.StringType)

  test("identity, swap, duplication, and projection") {
    assert(lambda[●, ●](a => a) == TypeFun.id[TC, ●])
    assert(lambdaN[●, ● × ●](a => a zip a) == MultiTypeFun.dup[TC, ●])
    assert(lambdaN[● × ●, ● × ●] { ab =>
      val zip(a, b) = ab
      b zip a
    } == MultiTypeFun.swap[TC, ●, ●])
    assert(lambda[● × ●, ●](ab => ab.unzip._1) == TypeFun.elimSnd[TC, ●, ●])
    assert(lambda[● × ●, ●](ab => ab.unzip._2) == TypeFun.elimFst[TC, ●, ●])
  }

  test("composite inputs can be duplicated and reassociated") {
    assert(lambdaN[● × ●, (● × ●) × (● × ●)](ab => ab zip ab) == MultiTypeFun.dup[TC, ● × ●])
    val f = lambdaN[(● × ●) × ●, ● × (● × ●)] { abc =>
      val zip(zip(a, b), c) = abc
      a zip (b zip c)
    }
    assert(f == MultiTypeFun.assocLR[TC, ●, ●, ●])
  }

  test("primitive application with shared input and multiple outputs") {
    val f = lambdaN[●, ● × ●] { a => pair(a zip a) zip a }
    val expected = MultiTypeFun.dup[TC, ●] > MultiTypeFun.par(MultiTypeFun.dup[TC, ●] > pair, TypeFun.id[TC, ●])
    assert(f == expected)
  }

  test("eta reduction of TypeFun and TypeExpr applications") {
    val f = lambda[● × ●, ●](ab => pair(ab))
    val g = lambda[● × ●, ●](ab => pairExpr(ab))
    assert(f == pair)
    assert(g == pair)
  }

  test("parallel primitive applications compose on both sides") {
    val diagonal = MultiTypeFun.dup[TC, ●] > pair
    val both = MultiTypeFun.par(diagonal, diagonal)
    val f = lambdaN[● × ●, ● × ●] { ab =>
      val (a, b) = both(ab).unzip
      pair(a zip a) zip pair(b zip b)
    }
    assert(f == (both > both))
  }

  test("constants can be combined with inputs on either side") {
    val f = lambdaN[●, ● × ●] { a => const(intType) zip a }
    val g = lambdaN[●, ● × ●] { a => a zip const(TypeFun.fromExpr(stringType)) }
    assert(f == MultiTypeFun.introFst[TC, ●, ●](TypeFun.fromExpr(intType)))
    assert(g == MultiTypeFun.introSnd[TC, ●, ●](TypeFun.fromExpr(stringType)))
  }

  test("constant results can discard the entire input") {
    val f = lambdaN[● × ●, ● × ●] { _ => const(intType) zip const(stringType) }
    val expected = MultiTypeFun.elim[TC, ● × ●] > MultiTypeFun.introBoth(intType, stringType)
    assert(f == expected)
  }

  test("a multi-output constant can be introduced and destructured") {
    val constant = MultiTypeFun.introBoth(intType, stringType)
    val f = lambdaN[●, ● × ●] { _ =>
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
    val keepBoth = lambdaN[● × ●, ● × ●] { ab =>
      val zip(zip(_, a), zip(b, _)) = addConstants(ab)
      a zip b
    }
    val keepFirst = lambdaN[● × ●, ● × ●] { ab =>
      val zip(zip(_, a), zip(_, s)) = addConstants(ab)
      a zip s
    }
    val keepSecond = lambdaN[● × ●, ● × ●] { ab =>
      val zip(zip(i, _), zip(b, _)) = addConstants(ab)
      i zip b
    }
    val keepNeither = lambdaN[● × ●, ● × ●] { ab =>
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
    lambdaN[●, ●] { a => escaped = Some(a); a }
    lambda[●, ●] { a => escaped = Some(a); a }
    val e = intercept[IllegalArgumentException] {
      lambdaN[●, ● × ●] { b => escaped.get zip b }
    }
    assert(e.getMessage.contains("Undefined variables"))
    assert(e.getMessage.contains("Lambda parameter"))
  }

  test("lambda inputs and mapped outputs must have non-empty kinds") {
    assertDoesNotCompile("""lambda[○, ○](a => a)""")
    assertDoesNotCompile("""lambda[●, ○](a => MultiTypeFun.elim[TC, ●](a))""")
  }
}
