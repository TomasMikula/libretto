package libretto.lambda

import libretto.lambda.CapturingFun.{Closure, NoCapture}
import libretto.lambda.Lambdas.LinearityViolation.{Overused, Unused}
import libretto.lambda.util.Validated.Invalid
import org.scalatest.funsuite.AnyFunSuite

class ArrowPendingInObjLambdasTests extends AnyFunSuite {
  import ArrowPendingInObjLambdasTests.*

  type Prepared = (Arr pendingIn Obj)
  def Prepared[A, B] = ArrowPendingInObj[Arr, Obj, A, B]

  private val linear = Lambdas[Prepared, Tuple2, String, String]()
  private val nonlinear = Lambdas[Prepared, Tuple2, String, String](
    universalSplit = Some([X] => (_: DummyImplicit) ?=> Prepared[X, (X, X)] { x =>
      (Arr(x, Obj.Pair(x, x), a => (a, a)), Obj.Pair(x, x))
    }),
    universalDiscard = Some([X, Y] => (_: DummyImplicit) ?=> (
      Prepared[(X, Y), Y] { xy =>
        val (x, y) = summon[Unzippable[Tuple2, Obj]].unzip(xy)
        (Arr(Obj.Pair(x, y), y, _._2), y)
      },
      Prepared[(Y, X), Y] { yx =>
        val (y, x) = summon[Unzippable[Tuple2, Obj]].unzip(yx)
        (Arr(Obj.Pair(y, x), y, _._1), y)
      },
    )),
  )

  private def closed[A, B](l: Lambdas[Prepared, Tuple2, String, String])(
    f: l.Context ?=> l.Expr[A] => l.Expr[B],
  )(using Obj[A]): Arr[A, B] =
    l.delambdifyFoldTopLevel("outer", "input", f).valueOr(es => fail(s"$es")) match {
      case NoCapture(f) => f.run(summon[Obj[A]])._1
      case Closure(_, _) => fail("Unexpected capture")
    }

  test("witnesses follow primitive results through existential intermediate types") {
    val f = closed[Int, Int](linear) { a =>
      val s = linear.Expr.map(a, ArrowPendingInObj.lift(Arr.of[Int, String](_.toString)))("string")
      linear.Expr.map(s, ArrowPendingInObj.lift(Arr.of[String, Int](_.length)))("length")
    }
    assert(f.run(1234) == 4)
  }

  test("pairing, unpairing, zipN, and shuffles preserve heterogeneous witnesses") {
    val f = closed[((Int, String), Boolean), (String, (Boolean, Int))](linear) { input =>
      val (is, b) = linear.Expr.unzip(input)("is", "b")
      val (i, s) = linear.Expr.unzip(is)("i", "s")
      linear.Expr.zipN(Tupled.atom(s) zip (Tupled.atom(b) zip Tupled.atom(i)))("result")
    }
    assert(f.run(((3, "hello"), true)) == ("hello", (true, 3)))
    assert(f.tgt == summon[Obj[(String, (Boolean, Int))]])
  }

  test("linearity violations retain variable and scope labels") {
    linear.delambdifyFoldTopLevel[Int, (Int, Int)]("scope", "input", a => linear.Expr.zip(a, a)("pair")) match {
      case Invalid(errors) =>
        errors.head match {
          case Overused(vars, scope) =>
            assert(vars.list.map(_.origin) == List("input"))
            assert(scope == "scope")
          case other => fail(s"Unexpected error: $other")
        }
      case other => fail(s"Expected overuse: $other")
    }

    linear.delambdifyFoldTopLevel[(Int, String), Int]("scope", "input", ab => linear.Expr.unzip(ab)("left", "right")._1) match {
      case Invalid(errors) =>
        errors.head match {
          case Unused(v, scope) =>
            assert(v.origin == "right")
            assert(scope == "scope")
          case other => fail(s"Unexpected error: $other")
        }
      case other => fail(s"Expected unused variable: $other")
    }
  }

  test("universal duplication and discard work on composite objects") {
    val f = closed[((Int, String), Boolean), ((Int, String), (Int, String))](nonlinear) { input =>
      val (is, _) = nonlinear.Expr.unzip(input)("is", "unused")
      nonlinear.Expr.zip(is, is)("duplicated")
    }
    assert(f.run(((7, "seven"), false)) == ((7, "seven"), (7, "seven")))

    val g = closed[(Boolean, (Int, String)), (Int, String)](nonlinear) { input =>
      nonlinear.Expr.unzip(input)("unused", "is")._2
    }
    assert(g.run((false, (7, "seven"))) == (7, "seven"))
  }

  test("multiple constants can replace an unused input") {
    val f = closed[Boolean, (Int, String)](nonlinear) { _ =>
      val i = nonlinear.Expr.const[Int](
        [X] => (_: DummyImplicit) ?=> Prepared[X, (Int, X)] { x =>
          (Arr(x, Obj.Pair(Obj.IntObj, x), a => (42, a)), Obj.Pair(Obj.IntObj, x))
        },
      )("integer")
      val s = nonlinear.Expr.const[String](
        [X] => (_: DummyImplicit) ?=> Prepared[X, (String, X)] { x =>
          (Arr(x, Obj.Pair(Obj.StringObj, x), a => ("hello", a)), Obj.Pair(Obj.StringObj, x))
        },
        [X] => (_: DummyImplicit) ?=> Prepared[X, (X, String)] { x =>
          (Arr(x, Obj.Pair(x, Obj.StringObj), a => (a, "hello")), Obj.Pair(x, Obj.StringObj))
        },
      )("string")
      nonlinear.Expr.zip(i, s)("constants")
    }
    assert(f.run(false) == (42, "hello"))
  }

  test("per-expression operations retain an explicitly discarded computation") {
    var evaluated = 0
    val f = closed[Int, Int](linear) { a =>
      linear.Context.registerSplit(a)(ArrowPendingInObj.lift(Arr.of[Int, (Int, Int)](i => (i, i))))
      val unused = linear.Expr.map(a, ArrowPendingInObj.lift(Arr.of[Int, String] { i =>
        evaluated += 1
        i.toString
      }))("unused computation")
      linear.Context.registerDiscard(unused)(
        [X] => (_: DummyImplicit) ?=> Prepared[(String, X), X] { sx =>
          val (_, x) = summon[Unzippable[Tuple2, Obj]].unzip(sx)
          (Arr(sx, x, _._2), x)
        },
        [X] => (_: DummyImplicit) ?=> Prepared[(X, String), X] { xs =>
          val (x, _) = summon[Unzippable[Tuple2, Obj]].unzip(xs)
          (Arr(xs, x, _._1), x)
        },
      )
      assert(linear.Context.getSplit(linear.Expr.resultVar(a)).nonEmpty)
      assert(linear.Context.exprDiscarders(unused).nonEmpty)
      a
    }
    assert(evaluated == 0)
    assert(f.run(12) == 12)
    assert(evaluated == 1)
  }

  test("nested prepared functions can be reapplied without witnesses for their captures") {
    val f = closed[(Int, String), (String, (Int, Boolean))](linear) { input =>
      val (i, s) = linear.Expr.unzip(input)("i", "s")
      val nested = linear.delambdifyFoldNested[Boolean, (String, (Int, Boolean))](
        "inner", "b", b => linear.Expr.zip(s, linear.Expr.zip(i, b)("ib"))("sib"),
      ).valueOr(es => fail(s"$es"))
      val b = linear.Expr.const[Boolean](
        [X] => (_: DummyImplicit) ?=> Prepared[X, (Boolean, X)] { x =>
          (Arr(x, Obj.Pair(Obj.BoolObj, x), a => (true, a)), Obj.Pair(Obj.BoolObj, x))
        },
      )("true")
      nested match {
        case Closure(captured, g) =>
          val captures = linear.Expr.zipN(captured)("captures")
          linear.Expr.map(linear.Expr.zip(captures, b)("argument"), g)("applied")
        case NoCapture(_) => fail("Expected a closure")
      }
    }
    assert(f.run((3, "hello")) == ("hello", (3, true)))
  }

  test("nested scopes inherit registered non-linear operations and constants") {
    val f = closed[Int, (Int, (Int, Boolean))](linear) { a =>
      linear.Context.registerSplit(a)(ArrowPendingInObj.lift(Arr.of[Int, (Int, Int)](i => (i, i))))
      val c = linear.Expr.const[Boolean](
        [X] => (_: DummyImplicit) ?=> Prepared[X, (Boolean, X)] { x =>
          (Arr(x, Obj.Pair(Obj.BoolObj, x), value => (true, value)), Obj.Pair(Obj.BoolObj, x))
        },
      )("constant")
      val nested = linear.delambdifyFoldNested[String, (Int, (Int, Boolean))](
        "inner", "unused", b => {
          linear.Context.registerDiscard(b)(
            [X] => (_: DummyImplicit) ?=> Prepared[(String, X), X] { sx =>
              val (_, x) = summon[Unzippable[Tuple2, Obj]].unzip(sx)
              (Arr(sx, x, _._2), x)
            },
            [X] => (_: DummyImplicit) ?=> Prepared[(X, String), X] { xs =>
              val (x, _) = summon[Unzippable[Tuple2, Obj]].unzip(xs)
              (Arr(xs, x, _._1), x)
            },
          )
          linear.Expr.zip(a, linear.Expr.zip(a, c)("ac"))("aac")
        },
      ).valueOr(es => fail(s"$es"))
      val s = linear.Expr.const[String](
        [X] => (_: DummyImplicit) ?=> Prepared[X, (String, X)] { x =>
          (Arr(x, Obj.Pair(Obj.StringObj, x), value => ("unused", value)), Obj.Pair(Obj.StringObj, x))
        },
      )("string")
      nested match {
        case Closure(captured, g) =>
          linear.Expr.map(linear.Expr.zip(linear.Expr.zipN(captured)("captures"), s)("argument"), g)("applied")
        case NoCapture(_) => fail("Expected a closure")
      }
    }
    assert(f.run(5) == (5, (5, true)))
  }

  test("free expressions from another top-level scope are reported before running arrows") {
    var escaped: Option[linear.Expr[Int]] = None
    closed[Int, Int](linear) { a => escaped = Some(a); a }
    val result = linear.delambdifyFoldTopLevel[String, (Int, String)](
      "second", "s", s => linear.Expr.zip(escaped.get, s)("result"),
    ).valueOr(es => fail(s"$es"))
    result match {
      case Closure(captured, _) =>
        assert(linear.Expr.initialVars(captured).list.map(_.origin) == List("input"))
      case NoCapture(_) => fail("Expected the free expression to be reported as a capture")
    }
  }
}

object ArrowPendingInObjLambdasTests {
  sealed trait Obj[A]
  object Obj {
    case object IntObj extends Obj[Int]
    case object StringObj extends Obj[String]
    case object BoolObj extends Obj[Boolean]
    case class Pair[A, B](a: Obj[A], b: Obj[B]) extends Obj[(A, B)]

    given Obj[Int] = IntObj
    given Obj[String] = StringObj
    given Obj[Boolean] = BoolObj
    given [A: Obj, B: Obj]: Obj[(A, B)] = Pair(summon, summon)

    given Unzippable[Tuple2, Obj] with {
      override def unzip[A, B](ab: Obj[(A, B)]): (Obj[A], Obj[B]) =
        ab match { case Pair(a, b) => (a, b) }
    }
  }

  case class Arr[A, B](src: Obj[A], tgt: Obj[B], run: A => B)
  object Arr {
    def of[A: Obj, B: Obj](run: A => B): Arr[A, B] = Arr(summon, summon, run)

    given (Arr Preserves Obj) with {
      override def apply[A: Obj, B](rel: Arr[A, B]): Obj[B] =
        rel.tgt
    }
  }

  given NarrowSymmetricSemigroupalCategory[Obj, Arr, Tuple2] with {
    override def tensor[A, B](a: Obj[A], b: Obj[B]): Obj[(A, B)] = Obj.Pair(a, b)
    override def id[A](using a: Obj[A]): Arr[A, A] = Arr(a, a, identity)

    override def narrowAndThen[A, B, C](f: Arr[A, B], g: Arr[B, C])(using a: Obj[A], b: Obj[B], c: Obj[C]): Arr[A, C] = {
      assert(f.src == a && f.tgt == b && g.src == b && g.tgt == c)
      Arr(a, c, f.run.andThen(g.run))
    }

    override def narrowPar[A1, A2, B1, B2](f: Arr[A1, B1], g: Arr[A2, B2])(using
      a1: Obj[A1], a2: Obj[A2], b1: Obj[B1], b2: Obj[B2],
    ): Arr[(A1, A2), (B1, B2)] = {
      assert(f.src == a1 && f.tgt == b1 && g.src == a2 && g.tgt == b2)
      Arr(Obj.Pair(a1, a2), Obj.Pair(b1, b2), (a, b) => (f.run(a), g.run(b)))
    }

    override def swap[A, B](using a: Obj[A], b: Obj[B]): Arr[(A, B), (B, A)] =
      Arr(Obj.Pair(a, b), Obj.Pair(b, a), _.swap)

    override def assocLR[A, B, C](using a: Obj[A], b: Obj[B], c: Obj[C]): Arr[((A, B), C), (A, (B, C))] =
      Arr(Obj.Pair(Obj.Pair(a, b), c), Obj.Pair(a, Obj.Pair(b, c)), { case ((a, b), c) => (a, (b, c)) })

    override def assocRL[A, B, C](using a: Obj[A], b: Obj[B], c: Obj[C]): Arr[(A, (B, C)), ((A, B), C)] =
      Arr(Obj.Pair(a, Obj.Pair(b, c)), Obj.Pair(Obj.Pair(a, b), c), { case (a, (b, c)) => ((a, b), c) })
  }
}
