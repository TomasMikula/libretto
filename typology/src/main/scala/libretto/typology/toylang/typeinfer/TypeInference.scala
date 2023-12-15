package libretto.typology.toylang.typeinfer

import libretto.lambda.util.{Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.terms.TypedFun.Type
import libretto.typology.toylang.types.{AbstractTypeLabel, ScalaTypeParam, TypeTag}
import libretto.typology.util.State

object TypeInference {
  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    println(s"inferTypes($f)")
    val t0 = System.currentTimeMillis()

    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    given tools: TypeInferencer[Either[ScalaTypeParam, AbstractTypeLabel]] =
      TypeInferencer.instance

    val res =
    reconstructTypes(f)
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          (f /*:>> alsoPrintLine(f => s"RESULT of reconstructTypes: $f")*/)
            .waitFor(tools.close(a) /*:>> printLine("INPUT closed")*/)
            .waitFor(tools.close(b) /*:>> printLine("OUTPUT closed")*/)
        }
      }
      .run(0)

    val t1 = System.currentTimeMillis()
    println(s"inferTypes assembly took ${t1 - t0}ms")
    res
  }

  def reconstructTypes[M[_], A, B](f: Fun[A, B])(using
    tools: TypeInferencer[Either[ScalaTypeParam, AbstractTypeLabel]],
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (tools.Tp |*| Val[TypedFun[A, B]] |*| tools.Tp)] = {
    // println(s"reconstructTypes($f)")
    import gen.newVar
    import tools.{apply1T, either, fixT, int, label, merge, output, pair, recCall, split, string, unit}

    val nested: tools.Nested = tools.nested
    import nested.{lower, tools => nt, unnest}

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (nt.Tp |*| Val[TypedFun[A, B]] |*| nt.Tp)] =
      TypeInference.reconstructTypes(f)(using nt)

    def newAbstractType(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[tools.Tp |*| Val[Type] |*| tools.Tp] =
      constant(label(Right(v))) :>> tools.abstractTypeTap :>> λ { case s |*| t =>
        val s1 |*| s2 = split(s)
        s1 |*| t |*| s2
      }

    def newTypeParam(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[tools.Tp |*| Val[Type]] =
      tools.abstractTypeTap(constant(label(Right(v))))

    f.value match {
      case FunT.IdFun() =>
        for {
          v <- newVar
        } yield
          λ.? { _ =>
            val a |*| t |*| b = newAbstractType(v)
            a |*| (t :>> mapVal(TypedFun.Id(_))) |*| b
          }
      case FunT.AndThen(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a |*| f |*| x1 = tf(one)
            val x2 |*| g |*| b = tg(one)
            val x = nt.output(nt.merge(x1 |*| x2))
            val h = (f ** x ** g) :>> mapVal { case ((f, x), g) => TypedFun.andThen(f, x, g) }
            nested.unnest(a) |*| h |*| nested.unnest(b)
          }
      case FunT.Par(f1, f2) =>
        for {
          tf1 <- reconstructTypes(f1)
          tf2 <- reconstructTypes(f2)
        } yield
          λ.* { one =>
            val a1 |*| f1 |*| b1 = tf1(one)
            val a2 |*| f2 |*| b2 = tf2(one)
            val a = nt.pair(a1 |*| a2)
            val b = nt.pair(b1 |*| b2)
            val f = (f1 ** f2) :>> mapVal { case (f1, f2) => TypedFun.par(f1, f2) }
            nested.unnest(a) |*| f |*| nested.unnest(b)
          }
      case _: FunT.AssocLR[arr, a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val c1 |*| tc |*| c2 = newAbstractType(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocLR[a, b, c](a, b, c) }
            val in  = pair(pair(a1 |*| b1) |*| c1)
            val out = pair(a2 |*| pair(b2 |*| c2))
            in |*| f |*| out
          }
        }
      case _: FunT.AssocRL[arr, a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val c1 |*| tc |*| c2 = newAbstractType(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocRL[a, b, c](a, b, c) }
            val in  = pair(a1 |*| pair(b1 |*| c1))
            val out = pair(pair(a2 |*| b2) |*| c2)
            in |*| f |*| out
          }
        }
      case _: FunT.Swap[arr, a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.swap[a, b](a, b) }
            val in  = pair(a1 |*| b1)
            val out = pair(b2 |*| a2)
            in |*| f |*| out
          }
        }
      case FunT.EitherF(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a1 |*| f |*| b1 = tf(one)
            val a2 |*| g |*| b2 = tg(one)
            val a = nt.either(a1 |*| a2)
            val b = nt.merge(b1 |*| b2)
            val h = (f ** g) :>> mapVal { case (f, g) => TypedFun.either(f, g) }
            unnest(a) |*| h |*| unnest(b)
          }
      case _: FunT.InjectL[arr, l, r] =>
        for {
          ll <- newVar
          rl <- newVar
        } yield
          λ.? { _ =>
            val l1 |*| lt |*| l2 = newAbstractType(ll)
            val r  |*| rt        = newTypeParam(rl)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = tools.either(l2 |*| r)
            (l1 |*| f |*| b)
          }
      case _: FunT.InjectR[arr, l, r] =>
        for {
          ll <- newVar
          rl <- newVar
        } yield
          λ.? { _ =>
            val  l |*| lt        = newTypeParam(ll)
            val r1 |*| rt |*| r2 = newAbstractType(rl)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = tools.either(l |*| r2)
            (r1 |*| f |*| b)
          }
      case _: FunT.Distribute[arr, a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val c1 |*| tc |*| c2 = newAbstractType(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.distribute[a, b, c](a, b, c) }
            val in  = pair(a1 |*| either(b1 |*| c1))
            val a3 |*| a4 = split(a2)
            val out = either(pair(a3 |*| b2) |*| pair(a4 |*| c2))
            in |*| f |*| out
          }
      case _: FunT.Dup[arr, a] =>
        for {
          a <- newVar
        } yield
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val a3 |*| a4 = split(a2)
            val f = ta :>> mapVal { a => TypedFun.dup[a](a) }
            a1 |*| f |*| pair(a3 |*| a4)
          }
      case _: FunT.Prj1[arr, a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb        = newTypeParam(b)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.prj1[a, b](a, b) }
            pair(a1 |*| b1) |*| f |*| a2
          }
      case _: FunT.Prj2[arr, a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield
          λ.? { _ =>
            val a1 |*| ta        = newTypeParam(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.prj2[a, b](a, b) }
            pair(a1 |*| b1) |*| f |*| b2
          }
      case f: FunT.FixF[arr, f] =>
        Monad[M].pure(
          λ.* { one =>
            val fixF = fixT[f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[f](f.f)(one))
            val tf = constantVal(TypedFun.fix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        Monad[M].pure(
          λ.* { one =>
            val fixF = fixT[f](f.f)(one)
            val fFixF = apply1T(f.f)(fixT[f](f.f)(one))
            val tf = constantVal(TypedFun.unfix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fixF |*| tf |*| fFixF
          }
        )
      case FunT.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            nt.isPair(nt.tap(aba)) switch {
              case Right(ab |*| a1) =>
                nt.isRecCall(ab) switch {
                  case Right(a0 |*| b0) =>
                    val a = merge(lower(a0) |*| lower(a1))
                    val b = merge(lower(b0) |*| unnest(b1))
                    val a_ |*| ta = tools.split(a) :>> snd(tools.output)
                    val h = (ta ** f) :>> mapVal { case (ta, f) =>
                      // println(s"OUTPUTTING arg of Rec: $f")
                      TypedFun.rec(ta, f)
                    }
                    a_ |*| h |*| b
                  case Left(ab) =>
                    // (ab |*| f |*| a1 |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
                    val d = (f ** output(lower(ab)) ** output(lower(a1)) ** output(unnest(b1)))
                      :>> printLine { case (((f, ab), a1), b) =>
                        s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=($ab, $a1), OUT-TYPE=$b"
                      }
                    d :>> fork :>> crashWhenDone(s"TODO (${summon[SourcePos]})")
                }
              case Left(aba) =>
                import scala.concurrent.duration._
                val d = (f ** output(lower(aba)) ** output(unnest(b1)))
                  :>> printLine { case ((f, aba), b) =>
                    s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=$aba, OUT-TYPE=$b"
                  }
                d :>> fork :>> crashWhenDone(s"TODO (${summon[SourcePos]})")
                // (d |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
            }
          }
      case _: FunT.Recur[arr, a, b] =>
        for {
          va <- newVar
          vb <- newVar
        } yield
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractType(va)
            val b1 |*| tb |*| b2 = newAbstractType(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = pair(recCall(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        Monad[M].pure(
          λ.* { one =>
            val a = done(one) :>> unit
            val b = done(one) :>> int
            val tf = constantVal(TypedFun.constInt(n))
            a |*| tf |*| b
          }
        )
      case FunT.AddInts() =>
        Monad[M].pure(
          λ.? { one =>
            val a1 = constant(done > int)
            val a2 = constant(done > int)
            val b  = constant(done > int)
            val tf = constantVal(TypedFun.addInts)
            pair(a1 |*| a2) |*| tf |*| b
          }
        )
      case FunT.IntToString() =>
        Monad[M].pure(
          λ.* { one =>
            val a = done(one) :>> int
            val b = done(one) :>> string
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
  }
}
