package libretto.typology.toylang.typeinfer

import libretto.lambda.util.{Monad, SourcePos}
import libretto.scaletto.StarterKit.*
import libretto.typology.inference.Propagator
import libretto.typology.toylang.terms.{Fun, TypedFun}
import libretto.typology.toylang.types.{AbstractTypeLabel, Label, ScalaTypeParam, Type, TypeConstructor, TypeTag}
import libretto.typology.util.{Either3, State}

object TypeInference {

  private given VarGen[State[Int, *], AbstractTypeLabel] with {
    override def newVar: State[Int, AbstractTypeLabel] =
      State(n => (n+1, AbstractTypeLabel(n)))
  }

  private given pg: Propagator[NonAbstractType[Val[Label], _], Type[Label], Label] =
    import NonAbstractType.given
    Propagator.instance[NonAbstractType[Val[Label], _], Type[Label], Label](Type.abstractType)

  {
    def go[F[_], T, L](i: Int, n: Int, pg: Propagator[F, T, L]): Unit =
      if (i < n) {
        println(s"Priming propagator level ${i+1}")
        val t0 = System.currentTimeMillis()
        val pgn = pg.nested.propagator
        val t1 = System.currentTimeMillis()
        println(s"  propagator took ${t1 - t0}ms")
        val merge = pgn.merge
        val t2 = System.currentTimeMillis()
        println(s"  merge took ${t2 - t1}ms")
        val split = pgn.split
        val t3 = System.currentTimeMillis()
        println(s"  split took ${t3 - t2}ms")
        println(s"  TOTAL: ${t3 - t0}ms")
        val mergeSize = sizeOf(merge)
        val splitSize = sizeOf(split)
        println("  size:")
        println(s"    merge: $mergeSize")
        println(s"    split: $splitSize")
        go(i+1, n, pgn)
      }

    go(0, 24, pg)
  }

  def inferTypes[A, B](f: Fun[A, B]): One -⚬ Val[TypedFun[A, B]] = {
    println(s"inferTypes($f)")
    val t0 = System.currentTimeMillis()

    val res =
    reconstructTypes(f)
      .map { prg =>
        prg > λ { case a |*| f |*| b =>
          f
            .waitFor(pg.close(a))
            .waitFor(pg.close(b))
        }
      }
      .run(0)

    val t1 = System.currentTimeMillis()
    println(s"inferTypes assembly took ${t1 - t0}ms")
    println(s"  size: ${sizeOf(res)}")
    res
  }

  def reconstructTypes[M[_], A, B](f: Fun[A, B])(using
    pg: Propagator[NonAbstractType[Val[Label], _], Type[Label], Label],
  )(using
    gen: VarGen[M, AbstractTypeLabel],
    M: Monad[M],
  ): M[One -⚬ (pg.Tp |*| Val[TypedFun[A, B]] |*| pg.Tp)] = {
    import gen.newVar
    import NonAbstractType.{Either, Int, Pair, RecCall, String, Unit}
    import pg.{Tp, TypeOutlet, label, merge, output, split}

    val nested: pg.Nested = pg.nested
    import nested.{lower, propagator as npg, unnest}

    def reconstructTypes[A, B](f: Fun[A, B]): M[One -⚬ (npg.Tp |*| Val[TypedFun[A, B]] |*| npg.Tp)] =
      TypeInference.reconstructTypes(f)(using npg)

    def newAbstractType(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[pg.Tp |*| Val[Type[Label]] |*| pg.Tp] =
      constant(label(Label.Abstr(v))) |> pg.abstractTypeTap > λ { case s |*| t =>
        val s1 |*| s2 = split(s)
        s1 |*| t |*| s2
      }

    def newTypeParam(v: AbstractTypeLabel)(using
      SourcePos,
      LambdaContext,
    ): $[pg.Tp |*| Val[Type[Label]]] =
      pg.abstractTypeTap(constant(label(Label.Abstr(v))))

    def liftType(t: Type[ScalaTypeParam]): One -⚬ Tp =
      NonAbstractType.lift(
        Tp,
        v => label(v) > pg.abstractTypeTap > snd(neglect) > awaitPosSnd,
        t,
      )

    f match {
      case Fun.IdFun() =>
        for {
          v <- newVar
        } yield
          λ { case ?(_) =>
            val a |*| t |*| b = newAbstractType(v)
            a |*| (t |> mapVal(TypedFun.Id(_))) |*| b
          }
      case Fun.AndThen(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ { case *(one) =>
            val a |*| f |*| x1 = tf(one)
            val x2 |*| g |*| b = tg(one)
            val x = npg.output(npg.merge(x1 |*| x2))
            val h = (f ** x ** g) |> mapVal { case ((f, x), g) => TypedFun.andThen(f, x, g) }
            nested.unnest(a) |*| h |*| nested.unnest(b)
          }
      case Fun.Par(f1, f2) =>
        for {
          tf1 <- reconstructTypes(f1)
          tf2 <- reconstructTypes(f2)
        } yield
          λ { case *(one) =>
            val a1 |*| f1 |*| b1 = tf1(one)
            val a2 |*| f2 |*| b2 = tf2(one)
            val a = npg.Tp(Pair(a1 |*| a2))
            val b = npg.Tp(Pair(b1 |*| b2))
            val f = (f1 ** f2) |> mapVal { case (f1, f2) => TypedFun.par(f1, f2) }
            nested.unnest(a) |*| f |*| nested.unnest(b)
          }
      case _: Fun.AssocLR[a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield {
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val c1 |*| tc |*| c2 = newAbstractType(c)
            val f = (ta ** tb ** tc) |> mapVal { case ((a, b), c) => TypedFun.assocLR[a, b, c](a, b, c) }
            val in  = Tp(Pair(Tp(Pair(a1 |*| b1)) |*| c1))
            val out = Tp(Pair(a2 |*| Tp(Pair(b2 |*| c2))))
            in |*| f |*| out
          }
        }
      case _: Fun.AssocRL[a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield {
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val c1 |*| tc |*| c2 = newAbstractType(c)
            val f = (ta ** tb ** tc) |> mapVal { case ((a, b), c) => TypedFun.assocRL[a, b, c](a, b, c) }
            val in  = Tp(Pair(a1 |*| Tp(Pair(b1 |*| c1))))
            val out = Tp(Pair(Tp(Pair(a2 |*| b2)) |*| c2))
            in |*| f |*| out
          }
        }
      case _: Fun.Swap[a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield {
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val f = (ta ** tb) |> mapVal { case (a, b) => TypedFun.swap[a, b](a, b) }
            val in  = Tp(Pair(a1 |*| b1))
            val out = Tp(Pair(b2 |*| a2))
            in |*| f |*| out
          }
        }
      case Fun.EitherF(f, g) =>
        for {
          tf <- reconstructTypes(f)
          tg <- reconstructTypes(g)
        } yield
          λ { case *(one) =>
            val a1 |*| f |*| b1 = tf(one)
            val a2 |*| g |*| b2 = tg(one)
            val a = npg.Tp(Either(a1 |*| a2))
            val b = npg.merge(b1 |*| b2)
            val h = (f ** g) |> mapVal { case (f, g) => TypedFun.either(f, g) }
            unnest(a) |*| h |*| unnest(b)
          }
      case _: Fun.InjectL[l, r] =>
        for {
          ll <- newVar
          rl <- newVar
        } yield
          λ { case ?(_) =>
            val l1 |*| lt |*| l2 = newAbstractType(ll)
            val r  |*| rt        = newTypeParam(rl)
            val f = (lt ** rt) |> mapVal { case (lt, rt) => TypedFun.injectL[l, r](lt, rt) }
            val b = pg.Tp(Either(l2 |*| r))
            (l1 |*| f |*| b)
          }
      case _: Fun.InjectR[l, r] =>
        for {
          ll <- newVar
          rl <- newVar
        } yield
          λ { case ?(_) =>
            val  l |*| lt        = newTypeParam(ll)
            val r1 |*| rt |*| r2 = newAbstractType(rl)
            val f = (lt ** rt) |> mapVal { case (lt, rt) => TypedFun.injectR[l, r](lt, rt) }
            val b = pg.Tp(Either(l |*| r2))
            (r1 |*| f |*| b)
          }
      case _: Fun.Distribute[a, b, c] =>
        for {
          a <- newVar
          b <- newVar
          c <- newVar
        } yield
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val c1 |*| tc |*| c2 = newAbstractType(c)
            val f = (ta ** tb ** tc) |> mapVal { case ((a, b), c) => TypedFun.distribute[a, b, c](a, b, c) }
            val in  = Tp(Pair(a1 |*| Tp(Either(b1 |*| c1))))
            val a3 |*| a4 = split(a2)
            val out = Tp(Either(Tp(Pair(a3 |*| b2)) |*| Tp(Pair(a4 |*| c2))))
            in |*| f |*| out
          }
      case _: Fun.Dup[a] =>
        for {
          a <- newVar
        } yield
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val a3 |*| a4 = split(a2)
            val f = ta |> mapVal { a => TypedFun.dup[a](a) }
            a1 |*| f |*| Tp(Pair(a3 |*| a4))
          }
      case _: Fun.Prj1[a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(a)
            val b1 |*| tb        = newTypeParam(b)
            val f = (ta ** tb) |> mapVal { case (a, b) => TypedFun.prj1[a, b](a, b) }
            Tp(Pair(a1 |*| b1)) |*| f |*| a2
          }
      case _: Fun.Prj2[a, b] =>
        for {
          a <- newVar
          b <- newVar
        } yield
          λ { case ?(_) =>
            val a1 |*| ta        = newTypeParam(a)
            val b1 |*| tb |*| b2 = newAbstractType(b)
            val f = (ta ** tb) |> mapVal { case (a, b) => TypedFun.prj2[a, b](a, b) }
            Tp(Pair(a1 |*| b1)) |*| f |*| b2
          }
      case f: Fun.FixF[f] =>
        val tf = TypeTag.toTypeFun(f.f)
        val tg = tf.vmap(Label.ScalaTParam(_))
        val res: TypedFun[A, B] = TypedFun.fix[f](tg)
        val fixF = Type.fix(tf)
        val fFixF = tf(fixF)

        Monad[M].pure(
          λ { case *(one) =>
            val a = constant(liftType(fFixF))
            val b = constant(liftType( fixF))
            a |*| constantVal(res) |*| b
          }
        )
      case f: Fun.UnfixF[f] =>
        val tf = TypeTag.toTypeFun(f.f)
        val tg = tf.vmap(Label.ScalaTParam(_))
        val res: TypedFun[A, B] = TypedFun.unfix[f](tg)
        val fixF = Type.fix(tf)
        val fFixF = tf(fixF)

        Monad[M].pure(
          λ { case *(one) =>
            val a = constant(liftType( fixF))
            val b = constant(liftType(fFixF))
            a |*| constantVal(res) |*| b
          }
        )
      case Fun.Rec(f) =>
        for {
          tf <- reconstructTypes(f)
        } yield
          tf > λ { case aba |*| f |*| b1 =>
            npg.peek(npg.tap(aba)) either {
              case Left(aba) =>
                NonAbstractType.isPair(aba) either {
                  case Right(ab |*| a1) =>
                    npg.peek(ab) either {
                      case Left(ab) =>
                        NonAbstractType.isRecCall(ab) either {
                          case Right(a0 |*| b0) =>
                            val a = merge(lower(a0) |*| lower(a1))
                            val b = merge(lower(b0) |*| unnest(b1))
                            val a_ |*| ta = pg.split(a) |> snd(pg.output)
                            val h = (ta ** f) |> mapVal { case (ta, f) =>
                              // println(s"OUTPUTTING arg of Rec: $f")
                              TypedFun.rec(ta, f)
                            }
                            a_ |*| h |*| b
                          case Left(ab) =>
                            // (ab |*| f |*| a1 |*| b1) |> crashNow(s"TODO (${summon[SourcePos]})")
                            val d = (f ** output(lower(npg.outlet(ab))) ** output(lower(a1)) ** output(unnest(b1)))
                              |> printLine { case (((f, ab), a1), b) =>
                                s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=($ab, $a1), OUT-TYPE=$b"
                              }
                            d |> fork > crashWhenDone(s"TODO (${summon[SourcePos]})")
                        }
                      case Right(ab) =>
                        (ab |*| a1 |*| f |*| b1) |> crashNow(s"TODO (${summon[SourcePos]})")
                    }
                  case Left(aba) =>
                    import scala.concurrent.duration.*
                    val d = (f ** output(lower(npg.outlet(aba))) ** output(unnest(b1)))
                      |> printLine { case ((f, aba), b) =>
                        s"FUNCTION=${scala.util.Try(f.toString)}, IN-TYPE=$aba, OUT-TYPE=$b"
                      }
                    d |> fork > crashWhenDone(s"TODO (${summon[SourcePos]})")
                }
              case Right(aba) =>
                (aba |*| f |*| b1) |> crashNow(s"TODO (${summon[SourcePos]})")
            }
          }
      case _: Fun.Recur[a, b] =>
        for {
          va <- newVar
          vb <- newVar
        } yield
          λ { case ?(_) =>
            val a1 |*| ta |*| a2 = newAbstractType(va)
            val b1 |*| tb |*| b2 = newAbstractType(vb)
            val tf = (ta ** tb) |> mapVal { case (ta, tb) => TypedFun.recur[a, b](ta, tb) }
            val tIn = Tp(Pair(Tp(RecCall(a1 |*| b1)) |*| a2))
            tIn |*| tf |*| b2
          }
      case Fun.ConstInt(n) =>
        Monad[M].pure(
          λ { case *(one) =>
            val a = Unit(done(one)) |> Tp
            val b = Int(done(one)) |> Tp
            val tf = constantVal(TypedFun.constInt(n))
            a |*| tf |*| b
          }
        )
      case Fun.AddInts() =>
        Monad[M].pure(
          λ { case ?(_) =>
            val a1 = constant(done > Int.reinject > Tp)
            val a2 = constant(done > Int.reinject > Tp)
            val b  = constant(done > Int.reinject > Tp)
            val tf = constantVal(TypedFun.addInts)
            Tp(Pair(a1 |*| a2)) |*| tf |*| b
          }
        )
      case Fun.IntToString() =>
        Monad[M].pure(
          λ { case *(one) =>
            val a = Int(done(one)) |> Tp
            val b = String(done(one)) |> Tp
            val tf = constantVal(TypedFun.intToString)
            a |*| tf |*| b
          }
        )
    }
  }
}
