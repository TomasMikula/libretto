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
            .waitFor(tools.closeGen(a))
            .waitFor(tools.closeGen(b))
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
  ): M[One -⚬ (tools.OutwardType |*| Val[TypedFun[A, B]] |*| tools.OutwardType)] = {
    println(s"reconstructTypes($f)")
    import gen.newVar
    import tools.{apply1TOW, fixTOW, intOW, label, outputGen  as output, pairOW, recCall, recCallOW, stringOW}
    import Tools.ToolsImpl.Type

    val nested: tools.Nested = tools.nested
    import nested.{tools => nt}

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (nt.OutwardType |*| Val[TypedFun[A, B]] |*| nt.OutwardType)] =
      TypeInference.reconstructTypes(f)(using nt)

    def newAbstractTypeG(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[tools.OutwardType |*| Val[Type] |*| tools.OutwardType] =
      constant(label(v)) :>> tools.newAbstractTypeGen

    def newTypeParam(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[Val[Type] |*| tools.OutwardType] =
      tools.newTypeParam(constant(label(v)))

    f.value match {
      case FunT.IdFun() =>
        for {
          v <- newVar
        } yield
          λ.? { _ =>
            val a |*| t |*| b = newAbstractTypeG(v)
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
            val x = nested.mergeZap(x1 |*| x2)
            val h = (f ** x ** g) :>> mapVal { case ((f, x), g) => TypedFun.andThen(f, x, g) }
            nested.unnestOutward(a) |*| h |*| nested.unnestOutward(b)
          }
      case FunT.Par(f1, f2) =>
        for {
          tf1 <- reconstructTypes(f1)
          tf2 <- reconstructTypes(f2)
        } yield
          λ.* { one =>
            val a1 |*| f1 |*| b1 = tf1(one)
            val a2 |*| f2 |*| b2 = tf2(one)
            val a = nt.pairOW(a1 |*| a2)
            val b = nt.pairOW(b1 |*| b2)
            val f = (f1 ** f2) :>> mapVal { case (f1, f2) => TypedFun.par(f1, f2) }
            nested.unnestOutward(a) |*| f |*| nested.unnestOutward(b)
          }
      case _: FunT.AssocLR[arr, a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)
            val c1 |*| tc |*| c2 = newAbstractTypeG(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocLR[a, b, c](a, b, c) }
            val in  = pairOW(pairOW(a1 |*| b1) |*| c1)
            val out = pairOW(a2 |*| pairOW(b2 |*| c2))
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
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)
            val c1 |*| tc |*| c2 = newAbstractTypeG(c)
            val f = (ta ** tb ** tc) :>> mapVal { case ((a, b), c) => TypedFun.assocRL[a, b, c](a, b, c) }
            val in  = pairOW(a1 |*| pairOW(b1 |*| c1))
            val out = pairOW(pairOW(a2 |*| b2) |*| c2)
            in |*| f |*| out
          }
        }
      case _: FunT.Swap[arr, a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield {
          λ.? { _ =>
            val a1 |*| ta |*| a2 = newAbstractTypeG(a)
            val b1 |*| tb |*| b2 = newAbstractTypeG(b)
            val f = (ta ** tb) :>> mapVal { case (a, b) => TypedFun.swap[a, b](a, b) }
            val in  = pairOW(a1 |*| b1)
            val out = pairOW(b2 |*| a2)
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
            val a = nt.eitherOW(a1 |*| a2)
            val b = nested.mergeLower(b1 |*| b2)
            val h = (f ** g) :>> mapVal { case (f, g) => TypedFun.either(f, g) }
            nested.unnestOutward(a) |*| h |*| b
          }
      case _: FunT.InjectL[arr, l, r] =>
        for {
          l <- newVar
          r <- newVar
        } yield
          λ.? { _ =>
            val l1 |*| lt |*| l2 = newAbstractTypeG(l)
            val        rt |*| r2 = newTypeParam(r)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = tools.eitherOW(l2 |*| r2)
            (l1 |*| f |*| b)
          }
      case _: FunT.InjectR[arr, l, r] =>
        for {
          l <- newVar
          r <- newVar
        } yield
          λ.? { _ =>
            val        lt |*| l2 = newTypeParam(l)
            val r1 |*| rt |*| r2 = newAbstractTypeG(r)
            val f = (lt ** rt) :>> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = tools.eitherOW(l2 |*| r2)
            (r1 |*| f |*| b)
          }
      case FunT.Distribute() =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case f: FunT.FixF[arr, f] =>
        Monad[M].pure(
          λ.* { one =>
            val fixF = fixTOW[f](f.f)(one)
            val fFixF = apply1TOW(f.f)(fixTOW[f](f.f)(one))
            val tf = constantVal(TypedFun.fix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fFixF |*| tf |*| fixF
          }
        )
      case f: FunT.UnfixF[arr, f] =>
        Monad[M].pure(
          λ.* { one =>
            val fixF = fixTOW[f](f.f)(one)
            val fFixF = apply1TOW(f.f)(fixTOW[f](f.f)(one))
            val tf = constantVal(TypedFun.unfix[f](TypeTag.toTypeFun(f.f).vmap(Left(_))))
            fixF |*| tf |*| fFixF
          }
        )
      case FunT.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            nt.isPairOW(aba) switch {
              case Right(ab |*| a1) =>
                nt.isRecCallOW(ab) switch {
                  case Right(a0 |*| b0) =>
                    val a = nested.mergeLower(a0 |*| a1)
                    val b = nested.mergeLower(b0 |*| b1)
                    val h = f :>> mapVal { TypedFun.rec(_) }
                    a |*| h |*| b
                  case Left(ab) =>
                    // (ab |*| f |*| a1 |*| b1) :>> crashNow(s"TODO (${summon[SourcePos]})")
                    val d = (f ** output(nested.unnestOutward(ab)) ** output(nested.unnestOutward(a1)) ** output(nested.unnestOutward(b1)))
                      :>> printLine { case (((f, ab), a1), b) =>
                        s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=($ab, $a1), OUT-TYPE=$b"
                      }
                    d :>> fork :>> crashWhenDone(s"TODO (${summon[SourcePos]})")
                }
              case Left(aba) =>
                import scala.concurrent.duration._
                val d = (f ** output(nested.unnestOutward(aba)) ** output(nested.unnestOutward(b1)))
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
            val a1 |*| ta |*| a2 = newAbstractTypeG(va)
            val b1 |*| tb |*| b2 = newAbstractTypeG(vb)
            val tf = (ta ** tb) :>> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = pairOW(recCallOW(a1 |*| b1) |*| a2)
            tIn |*| tf |*| b2
          }
      case FunT.ConstInt(n) =>
        throw NotImplementedError(s"at ${summon[SourcePos]}")
      case FunT.AddInts() =>
        Monad[M].pure(
          λ.? { one =>
            val a1 = constant(done > intOW)
            val a2 = constant(done > intOW)
            val b  = constant(done > intOW)
            val tf = constantVal(TypedFun.addInts)
            pairOW(a1 |*| a2) |*| tf |*| b
          }
        )
      case FunT.IntToString() =>
        Monad[M].pure(
          λ.* { one =>
            val a = done(one) :>> intOW
            val b = done(one) :>> stringOW
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
  }
}
