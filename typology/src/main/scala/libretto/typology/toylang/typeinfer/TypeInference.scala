package libretto.typology.toylang.typeinfer

import libretto.lambda.util.{Monad, SourcePos}
import libretto.lambda.util.Monad.syntax._
import libretto.scaletto.StarterKit._
import libretto.typology.toylang.terms.{Fun, FunT, TypedFun}
import libretto.typology.toylang.types.{AbstractTypeLabel, TypeTag}
import libretto.typology.util.State

object TypeInference {
  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    println(s"inferTypes($f)")
    val t0 = System.currentTimeMillis()

    given VarGen[State[Int, *], AbstractTypeLabel] with {
      override def newVar: State[Int, AbstractTypeLabel] =
        State(n => (n+1, AbstractTypeLabel(n)))
    }

    given tools: Tools = Tools.instance

    val res =
    reconstructTypes(f)
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          f
            .waitFor(tools.close(a))
            .waitFor(tools.close(b))
        }
      }
      .run(0)

    val t1 = System.currentTimeMillis()
    println(s"inferTypes assembly took ${t1 - t0}ms")
    res
  }

  def reconstructTypes[M[_], A, B](f: Fun[A, B])(using
    tools: Tools,
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (tools.OutboundType |*| Val[TypedFun[A, B]] |*| tools.OutboundType)] = {
    println(s"reconstructTypes($f)")
    import gen.newVar
    import tools.{apply1T, fixT, int, label, output, outputOW, pair, pairOW, recCall, recCallOW, string}
    import Tools.ToolsImpl.Type

    val nested: tools.Nested = tools.nested
    import nested.{tools => nt, unnest, unnestS, unnestM}

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (nt.OutboundType |*| Val[TypedFun[A, B]] |*| nt.OutboundType)] =
      TypeInference.reconstructTypes(f)(using nt)

    def newAbstractType(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[nt.SplittableType |*| Val[Type] |*| nt.SplittableType] =
      constant(nt.label(v)) :>> nt.abstractTypeSplit

    def newTypeParam(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[tools.OutboundType |*| Val[Type]] =
      tools.abstractTypeTap(constant(label(v)))

    f.value match {
      case FunT.IdFun() =>
        for {
          v <- newVar
        } yield
          λ.? { _ =>
            val a |*| t |*| b = newAbstractType(v)
            unnestS(a) |*| (t :>> mapVal(TypedFun.Id(_))) |*| unnestS(b)
          }
      case FunT.AndThen(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ.* { one =>
            val a |*| f |*| x1 = tf(one)
            val x2 |*| g |*| b = tg(one)
            val x = nt.outputM(nt.merge(nt.mergeable(x1) |*| nt.mergeable(x2)))
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
            val in  = pair(pair(unnestS(a1) |*| unnestS(b1)) |*| unnestS(c1))
            val out = pair(unnestS(a2) |*| pair(unnestS(b2) |*| unnestS(c2)))
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
            val in  = pair(unnestS(a1) |*| pair(unnestS(b1) |*| unnestS(c1)))
            val out = pair(pair(unnestS(a2) |*| unnestS(b2)) |*| unnestS(c2))
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
            val in  = pair(unnestS(a1) |*| unnestS(b1))
            val out = pair(unnestS(b2) |*| unnestS(a2))
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
            val b = nt.merge(nt.mergeable(b1) |*| nt.mergeable(b2))
            val h = (f ** g) :>> mapVal { case (f, g) => TypedFun.either(f, g) }
            unnest(a) |*| h |*| unnestM(b)
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
            val b = tools.either(unnestS(l2) |*| r)
            (unnestS(l1) |*| f |*| b)
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
            val b = tools.either(l |*| unnestS(r2))
            (unnestS(r1) |*| f |*| b)
          }
      case FunT.Distribute() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
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
                    val a = nested.mergeLower(a0 |*| a1)
                    val b = nested.mergeLower(b0 |*| nt.tap(b1))
                    val h = f :>> mapVal { TypedFun.rec(_) }
                    a |*| h |*| b
                  case Left(ab) =>
                    // (ab |*| f |*| a1 |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
                    val d = (f ** outputOW(nested.unnestOutward(ab)) ** outputOW(nested.unnestOutward(a1)) ** output(nested.unnest(b1)))
                      :>> printLine { case (((f, ab), a1), b) =>
                        s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=($ab, $a1), OUT-TYPE=$b"
                      }
                    d :>> fork :>> crashWhenDone(s"TODO (${summon[SourcePos]})")
                }
              case Left(aba) =>
                import scala.concurrent.duration._
                val d = (f ** outputOW(nested.unnestOutward(aba)) ** output(nested.unnest(b1)))
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
            val tIn = pair(recCall(unnestS(a1) |*| unnestS(b1)) |*| unnestS(a2))
            tIn |*| tf |*| unnestS(b2)
          }
      case FunT.ConstInt(n) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
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
