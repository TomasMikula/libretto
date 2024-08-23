package libretto

import java.util.concurrent.{Executors, ScheduledExecutorService}
import java.util.concurrent.atomic.AtomicInteger
import libretto.cats.Functor.*
import libretto.crash.CrashLib
import libretto.lambda.util.SourcePos
import libretto.puro.PuroLib
import libretto.scaletto.ScalettoLib
import libretto.testing.{TestCase, TestExecutor, TestKit}
import libretto.testing.scaletto.{ScalettoTestExecutor, ScalettoTestKit}
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite
import libretto.util.Async
import scala.collection.immutable.{:: as NonEmptyList}
import scala.compiletime.uninitialized
import scala.concurrent.{Await, Promise}
import scala.concurrent.duration.*

class BasicTests extends ScalatestScalettoTestSuite {
  private var scheduler: ScheduledExecutorService = uninitialized

  protected override def beforeAll(): Unit = {
    super.beforeAll()
    scheduler = Executors.newScheduledThreadPool(1)
  }

  protected override def afterAll(): Unit = {
    scheduler.shutdownNow()
    super.afterAll()
  }

  private def delayedAsync[A](d: FiniteDuration)(a: => A): Async[A] = {
    val p = Promise[A]()
    scheduler.schedule({ () => p.success(a) }: Runnable, d.length, d.unit)
    Async.fromFuture(p.future).map(_.get)
  }

  override def testExecutors: List[TestExecutor.Factory[ScalettoTestKit]] =
    List(
      ScalettoTestExecutor.defaultFactory,
    )

  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{Outcome, dsl, manualClock}
    import dsl.*
    val puroLib = PuroLib(dsl)
    val scalettoLib = ScalettoLib(dsl: dsl.type, puroLib)
    val crashLib = CrashLib(dsl)
    import puroLib.{*, given}
    import scalettoLib.{*, given}
    import crashLib.{leftOrCrash, rightOrCrash}
    import kit.bridge.Execution
    import Outcome.assertEquals
    import Outcome.monadOutcome.*

    def raceKeepWinner[A](
      prg1: Done -⚬ Val[A],
      prg2: Done -⚬ Val[A],
    ): Done -⚬ Val[A] =
      forkMap(prg1, prg2)
        > raceSwitch(
          caseFstWins = snd(neglect) > awaitPosSnd,
          caseSndWins = fst(neglect) > awaitPosFst,
        )

    List(
      "done" -> TestCase.awaitDone {
        introFst(done) > join
      },

      "join ⚬ fork" -> TestCase.awaitDone {
        fork > join
      },

      "notifyDoneR, forkPing, joinPing, strengthenPing, join" -> TestCase.awaitDone {
        notifyDoneR > snd(forkPing > joinPing > strengthenPing) > join
      },

      "joinNeed, strengthenPong, joinPong, forkPong, notifyNeedR" -> TestCase
        .awaitDone {
          def unreverse(prg: Need -⚬ Need): Done -⚬ Done =
            introSnd(lInvertSignal > fst(prg)) > assocRL > elimFst(rInvertSignal)

          unreverse(joinNeed > snd(strengthenPong > joinPong > forkPong) > notifyNeedR)
        },

      "constVal" -> TestCase
        .awaitVal { constVal(5) }
        .checkThat { assertEquals(_, 5) },

      "unliftEither" -> TestCase
        .awaitVal { constVal(42) > injectR > unliftEither }
        .checkThat { assertEquals(_, Right(42)) },

      "liftPair, liftNegPair" -> TestCase.awaitVal {
        val prg: Done -⚬ Val[(String, Int)] =
          id                                       [       Done                                                                           ]
            .>(constVal(("foo", 42)))           .to[     Val[(String, Int)]                                                               ]
            .>(introSnd(promise))               .to[     Val[(String, Int)]      |*| (   Neg[(String, Int)]       |*| Val[(String, Int)]) ]
            .>(assocRL)                         .to[ (   Val[(String, Int)]      |*|     Neg[(String, Int)]     ) |*| Val[(String, Int)]  ]
            .>(fst(par(liftPair, liftNegPair))) .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| Val[(String, Int)]  ]
            .>(fst(rInvert)).>(elimFst)         .to[                                                                  Val[(String, Int)]  ]

        prg
      }.checkThat {
        assertEquals(_, ("foo", 42))
      },

      "unliftPair, unliftNegPair" -> TestCase.awaitVal {
        val lInvert: One -⚬ ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) =
          puroLib.lInvert

        val prg: Done -⚬ Val[(String, Int)] =
          id                                              [               Done                                                                           ]
            .>(forkMap(constVal("foo"), constVal(42))) .to[   Val[String] |*| Val[Int]                                                                   ]
            .>(introSnd).>(snd(lInvert))               .to[  (Val[String] |*| Val[Int]) |*| ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) ]
            .>(assocRL)                                .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| (Val[String] |*| Val[Int])  ]
            .>(fst(par(unliftPair, unliftNegPair)))    .to[ (    Val[(String, Int)]     |*|      Neg[(String, Int)]    ) |*| (Val[String] |*| Val[Int])  ]
            .>(elimFst(fulfill))                       .to[                                                                   Val[String] |*| Val[Int]   ]
            .>(unliftPair)                             .to[                                                                      Val[(String, Int)]      ]

        prg
      }.checkThat {
         assertEquals(_, ("foo", 42))
      },

      "inflate" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          id                                 [    Done                           ]
            .>(constVal(42))              .to[  Val[Int]                         ]
            .>(introSnd(lInvertSignal))   .to[  Val[Int] |*| ( Need    |*| Done) ]
            .>(assocRL)                   .to[ (Val[Int] |*|   Need  ) |*| Done  ]
            .>(fst(snd(inflate)))         .to[ (Val[Int] |*| Neg[Int]) |*| Done  ]
            .>(elimFst(fulfill))          .to[                             Done  ]

        prg
      },

      "delayed injectL" -> TestCase
        .interactWith {
          // the Done on the out-port must not appear until the Need is supplied
          val prg: Done -⚬ (Need |*| (Done |+| Nothing)) =
            λ { start =>
              val n |*| d = constant(lInvertSignal)
              val res = (d |*| start) |> awaitInjectL
              n |*| res
            }
          prg
        }
        .via { port =>
          val (need, res0) = port.unzip()
          val (ping, res1) = res0.append(notifyEither).unzip()
          for {
            _ <- ping.expectNoPingThenIgnore(10.millis)
            _ = need.supplyNeed()
            d <- res1.expectLeft
            _ <- d.expectDone
          } yield ()
        },

      "delayed chooseL" -> TestCase.awaitVal {
        // 'A' delayed by 40 millis
        val a: Done -⚬ Val[Char] =
          delay(40.millis) > constVal('A')

        // 'B' delayed by 30 + 20 = 50 millis.
        // We are testing that the second timer starts ticking only after the delayed choice is made.
        val b: Done -⚬ Val[Char] =
          forkMap(delay(30.millis), choice(delay(20.millis), id)) > awaitPosChooseL > constVal('B')

        raceKeepWinner(a, b)
      }.checkThat {
         assertEquals(_, 'A')
      },

      "crashd" -> TestCase
        .interactWith(crashd("boom!"))
        .via { port =>
          for {
            e <- port.expectCrashDone
            _ <- Outcome.assertEquals(e.getMessage, "boom!")
          } yield ()
        },

      "crashd waits for its trigger" -> {
        val prg: Done -⚬ ((Done |*| Done) |+| (Done |*| Done)) =
          fork
            .>(fst(delay(10.millis) > crashd("Boom!")))
            .>( race )

        TestCase
          .interactWith(prg)
          .via { port =>
            for {
              rightPort       <- port.expectRight
              ports           = rightPort.unzip()
              (pCrash, pDone) = ports
              _               <- pDone.expectDone
              _               <- pCrash.expectCrashDone
            } yield ()
          }
      },

      "crashd - even if it loses a race, the program still crashes" -> TestCase
        .interactWith {
          id[Done]
            .>( forkMap(id, delay(10.millis) > crashd("oops")) )
            .>( raceDone )
            .>( either(id, id) )
        }
        .via { port =>
          for {
            e <- port.expectCrashDone
            _ <- Outcome.assertEquals(e.getMessage, "oops")
          } yield ()
        },

      "crashd in non-executed |+| has no effect" -> TestCase.awaitDone {
        injectL[Done, Done] > either(id, crashd("bang!"))
      },

      "crashd in non-chosen |&| alternative has no effect" -> TestCase.awaitDone {
        choice(id, crashd("bang!")) > chooseL
      },

      "coDistribute" -> {
        type B = Val[Boolean]
        type C = Val[Char]
        type I = Val[Int]
        type S = Val[String]

        case class Combination[X, Y](
          choose1: (B |&| C) -⚬ Val[X],
          choose2: (I |&| S) -⚬ Val[Y],
          expectedX: X,
          expectedY: Y,
        ) {
          type T = X
          type U = Y

          def go: ((B |&| C) |*| (I |&| S)) -⚬ Val[(T, U)] =
            par(choose1, choose2) > unliftPair

          def expected: (T, U) =
            (expectedX, expectedY)
        }

        //                (false   1)    (true "foo")    ('a'    2)    ('b'  "bar")
        val init: Done -⚬ (((B |*| I) |&| (B |*| S)) |&| ((C |*| I) |&| (C |*| S))) =
          choice(
            choice(
              forkMap(constVal(false), constVal(1)),
              forkMap(constVal(true), constVal("foo")),
            ),
            choice(
              forkMap(constVal('a'), constVal(2)),
              forkMap(constVal('b'), constVal("bar")),
            ),
          )

        val coDistributed1: Done -⚬ ((B |&| C) |*| (I |&| S)) =
          init
            .>(|&|.bimap(coDistributeL, coDistributeL))
            .>(coDistributeR)

        val coDistributed2: Done -⚬ ((B |&| C) |*| (I |&| S)) =
          init                                          .to[ ((B |*| I) |&| (B  |*|  S)) |&| ((C |*| I) |&| (C  |*| S)) ]
            .>(|&|.IXI)                                 .to[ ((B |*| I) |&| (C  |*|  I)) |&| ((B |*| S) |&| (C  |*| S)) ]
            .>(|&|.bimap(coDistributeR, coDistributeR)) .to[ ((B        |&|  C) |*|  I ) |&| ((B        |&|  C) |*| S ) ]
            .>(coDistributeL)                           .to[  (B        |&|  C) |*| (I   |&|                        S ) ]

        val combinations = Seq(
          Combination(chooseL, chooseL, false, 1),
          Combination(chooseL, chooseR, true, "foo"),
          Combination(chooseR, chooseL, 'a', 2),
          Combination(chooseR, chooseR, 'b', "bar"),
        )

        val cases =
          for {
            (f, i) <- Seq(coDistributed1, coDistributed2).zipWithIndex
            c <- combinations
          } yield {
            s"${i+1}.$c" -> TestCase
              .awaitVal { f > c.go }
              .checkThat { assertEquals(_, c.expected) }
          }

        TestCase.multiple(cases*)
      },

      "LList.splitEvenOdd" -> TestCase.awaitVal {
        val prg: Done -⚬ Val[(List[Int], List[Int])] =
          constListOf1(0, (1 to 20)*) > LList.splitEvenOdd > par(toScalaList, toScalaList) > unliftPair

        prg
      }.checkThat {
        assertEquals(_, (0 to 20).toList.partition(_ % 2 == 0))
      },

      "LList.halfRotateL" -> TestCase.awaitVal {
        val prg: Done -⚬ Val[List[(Int, Int)]] =
          constListOf1((0, 1), (2, 3), (4, 5))
            .>(LList.map(liftPair))
            .>(LList.halfRotateL)
            .>(LList.map(unliftPair))
            .>(toScalaList)

        prg
      }.checkThat {
        assertEquals(_, List((1, 2), (3, 4), (5, 0)))
      },

      "acquire - effect - transform - release" -> {
        class MVar[A](var value: A) {
          def set(a: A): MVar[A] = {
            this.value = a
            this
          }
        }

        val acquireFuns = Seq[Val[Int] -⚬ Res[MVar[Int]]](
          mVal(new MVar(_)),
          acquire0(new MVar(_), release = None),
          acquireAsync0(i => Async.defer(new MVar(i)), release = None),
        )

        val incFuns = Seq[Res[MVar[Int]] -⚬ Res[MVar[Int]]](
          effect0(i => i.set(i.value + 1)),
          effectAsync0(i => Async.defer(i.set(i.value + 1))),
          introSnd(const(())) > effect     [MVar[Int], Unit, Unit]((i, _) =>             i.set(i.value + 1) ) > effectWrAsync((_, _) => Async.defer(())),
          introSnd(const(())) > effectAsync[MVar[Int], Unit, Unit]((i, _) => Async.defer(i.set(i.value + 1))) > effectWr     ((_, _) =>             () ),
        )

        val toStringTrans = Seq[Res[MVar[Int]] -⚬ Res[MVar[String]]](
          transformResource0(i => new MVar(Integer.toString(i.value)), release = None),
          transformResourceAsync0(i => Async.defer(new MVar(Integer.toString(i.value))), release = None),
        )

        val releaseFuns = Seq[Res[MVar[String]] -⚬ Val[String]](
          release0(_.value),
          releaseAsync0(s => Async.defer(s.value)),
        )

        val cases =
          for {
            (acquireMVar,  i) <- acquireFuns   .zipWithIndex
            (incMVar,      j) <- incFuns       .zipWithIndex
            (mvarToString, k) <- toStringTrans .zipWithIndex
            (releaseMVar,  l) <- releaseFuns   .zipWithIndex
          } yield {
            val prg: Done -⚬ Val[String] =
              constVal(0)
                .>(acquireMVar)
                .>(incMVar)
                .>(mvarToString)
                .>(releaseMVar)

            s"$i.$j.$k.$l" -> TestCase
              .awaitVal { prg }
              .checkThat { assertEquals(_, "1") }
          }

        TestCase.multiple(cases*)
      },

      "release via registered function" -> {
        val ref = new java.util.concurrent.atomic.AtomicReference[String]("init")

        TestCase.interactWith {
          val prg: Done -⚬ Done =
            constVal(()) > acquire0(identity, release = Some(_ => ref.set("released"))) > release

          prg
        }.via { port =>
          port.expectDone >> {
            ref.get() match {
              case "released" => Outcome.success(())
              case other      => Outcome.failure(s"Unexpected value: '$other'")
            }
          }
        }
      },

      "splitResource" -> {
        val store = new java.util.concurrent.atomic.AtomicReference[List[String]](Nil)

        def log(s: String): Unit =
          store.updateAndGet(s :: _)

        TestCase
          .interactWith {
            val prg: Done -⚬ Done =
              constVal(())
                .>(acquire0[Unit, Unit](
                  acquire = _ => log("acquire A"),
                  release = Some(_ => log("release A")), // this release function should never be invoked
                ))
                .>(splitResource0(
                  _ => { log("split A -> (B, C)"); ((), ()) },
                  release1 = Some(_ => log("release B")),
                  release2 = Some(_ => log("release C")),
                ))
                .>(par(release, release))
                .>(join)

            prg
          }
          .via { port =>
            port.expectDone >> {
              val logEntries: List[String] = store.get().reverse

              Outcome.assertEquals(logEntries.take(2),       List("acquire A", "split A -> (B, C)")) >>
              Outcome.assertEquals(logEntries.drop(2).toSet, Set("release B", "release C")) >>
              Outcome.assertEquals(logEntries.size,          4)
            }
          }
      },

      "splitResourceAsync: check that resources are released if program crashes during their async acquisition" -> {
        val store = new java.util.concurrent.atomic.AtomicReference[List[String]](Nil)

        def log(s: String): Unit =
          store.updateAndGet(s :: _)

        val pb, pc = Promise[Unit]()

        val mainThread: Done -⚬ Done =
          constVal(())
            .>(acquire0[Unit, Unit](
              acquire = _ => log("acquire A"),
              release = Some(_ => log("release A")), // this release function should never be invoked
            ))
            .>(splitResourceAsync0(
              _ => delayedAsync(10.millis) { // there will be a crash within these 10ms it takes to split the resource into two
                log("split A -> (B, C)")
                ((), ())
              },
              release1 = Some({ _ => log("release B"); pb.success(()); Async.now(()) }),
              release2 = Some({ _ => log("release C"); pc.success(()); Async.now(()) }),
            ))
            .>(par(
              release0[Unit, Unit](_ => log("release B XXX")) > neglect, // this release function should never be invoked
              release0[Unit, Unit](_ => log("release C XXX")) > neglect, // this release function should never be invoked
            ))
            .>(join)

        val crashThread: Done -⚬ Done =
          delay(5.millis) > crashd("Boom!") // delay crash to give chance for resource split to begin

        val prg: Done -⚬ Done =
          forkMap(crashThread, mainThread) > join

        TestCase
          .interactWith(prg)
          .via(
            port =>
              for {
                e <- port.expectCrashDone
                _ <- Outcome.assertEquals(e.getMessage, "Boom!")
              } yield (),
            postStop = _ => {
              // The current implementation based on Futures does not guarantee that all processing has finished by the time
              // the program returns an error. Therefore, explicitly await completion of the release functions.
              Await.ready(pb.future zip pc.future, 1.second)

              val logEntries: List[String] = store.get().reverse

              for {
                _ <- Outcome.assertEquals(logEntries.take(2), List("acquire A", "split A -> (B, C)"))
                _ <- Outcome.assertEquals(logEntries.drop(2).toSet, Set("release B", "release C"))
                _ <- Outcome.assertEquals(logEntries.size, 4)
              } yield ()
            },
          )
      },

      "RefCounted" -> {
        import java.util.concurrent.atomic.AtomicInteger

        val releaseCounter = new AtomicInteger(0)
        val incGetClose: RefCounted[AtomicInteger] -⚬ Val[Int] =
          introSnd(const(()))                                       .to[ RefCounted[AtomicInteger] |*| Val[Unit] ]
            .>( RefCounted.effect((i, _) => i.incrementAndGet) )    .to[ RefCounted[AtomicInteger] |*| Val[Int]  ]
            .>(fst(RefCounted.release) > awaitPosFst)               .to[                               Val[Int]  ]

        val prg: Done -⚬ Val[Int] =
          constVal(0)
            .>(RefCounted.acquire0(new AtomicInteger(_), _ => releaseCounter.incrementAndGet))
            .>(RefCounted.dupRef)
            .>(snd(RefCounted.dupRef))
            .>(par(incGetClose, par(incGetClose, incGetClose)))
            .>(snd(unliftPair > mapVal(t => t._1 + t._2)))
            .>(unliftPair > mapVal(t => t._1 + t._2))

        TestCase
          .interactWith(prg)
          .via { port =>
            for {
              res <- port.expectVal
              _   <- Outcome.assertEquals(res, 6)
              _   <- Outcome.assertEquals(releaseCounter.get(), 1)
            } yield ()
          }
      },

      "blocking" -> {
        val n = 10
        val sleepMillis = 10

        case class Millis(value: Long)

        val currentTimeMillis: Done -⚬ Val[Millis] =
          constVal(()) > mapVal(_ => Millis(System.currentTimeMillis()))

        val sleep: Done -⚬ Val[Millis] =
          constVal(()) > blocking(_ => Thread.sleep(sleepMillis)) > mapVal(_ => Millis(System.currentTimeMillis()))

        val timed: Done -⚬ Val[(List[Millis], List[Millis])] = {
          // true, false, true, false, ...
          val alternating: NonEmptyList[Boolean] = (0 until (2*n)).map(_ % 2 == 0).toList.asInstanceOf[NonEmptyList[Boolean]]

          constList1(alternating)
            .>(LList1.toLList)
            .>(LList.map(liftBoolean))
            .>(LList.map(Bool.switch(caseTrue = sleep, caseFalse = currentTimeMillis)))
            .>(LList.splitEvenOdd)
            .>(par(toScalaList, toScalaList))
            .>(unliftPair)
        }

        val prg: Done -⚬ Val[(Millis, (List[Millis], List[Millis]))] =
          forkMap(currentTimeMillis, timed) > unliftPair

        TestCase
          .interactWith(prg)
          .via { port =>
            for {
              results <- port.expectVal

              (startMillis, (sleepEnds, pureEnds)) = results
              sleepDurations = sleepEnds.map(_.value - startMillis.value)
              pureDurations = pureEnds.map(_.value - startMillis.value)

              _ <- Outcome.assert(
                      sleepDurations.min >= sleepMillis,
                      s"sanity check failed: one of the blocking computations took only ${sleepDurations.min}ms, despite it having slept for ${sleepMillis}ms",
                    )

              // check that none of the non-blocking computations is blocked by any of the blocking computations,
              // by checking that it completed before any of the blocking computations could
              _ <- Outcome.assert(pureDurations.max < sleepMillis)
            } yield ()
          }
      },

      "LList.sortBySignal" -> {
        val delays =
          List(30, 20, 10, 50, 40, 0)

        val elems: NonEmptyList[Done -⚬ Val[Int]] =
          delays
            .map(n => delay(n.millis) > constVal(n))
            .asInstanceOf[NonEmptyList[Done -⚬ Val[Int]]]

        val prg: Done -⚬ LList[Val[Int]] =
          id                               [       Done       ]
            .>(LList1.from(elems))      .to[ LList1[Val[Int]] ]
            .>(LList1.toLList)          .to[  LList[Val[Int]] ]
            .>(LList.sortBySignal)      .to[  LList[Val[Int]] ]

        def expectNext(using e: Execution)(port: e.OutPort[LList[Val[Int]]], value: Int)(using SourcePos): Outcome[e.OutPort[LList[Val[Int]]]] =
          for {
            ht <- port.append(LList.uncons).expectRight
            (h, t) = ht.unzip()
            h <- h.expectVal
            _ <- Outcome.assertEquals(h, value)
          } yield t

        def expectNil(using e: Execution)(port: e.OutPort[LList[Val[Int]]])(using SourcePos): Outcome[Unit] =
          port
            .append(LList.uncons)
            .expectLeft
            .map(_.discardOne())

        TestCase
          .configure(manualClock)
          .interactWith(prg)
          .via { (port, clock) =>
            for {
              t <- expectNext(port, 0)
              _ = clock.advanceTo(15.millis)
              t <- expectNext(t, 10)
              _ = clock.advanceTo(25.millis)
              t <- expectNext(t, 20)
              _ = clock.advanceTo(35.millis)
              t <- expectNext(t, 30)
              _ = clock.advanceTo(45.millis)
              t <- expectNext(t, 40)
              _ = clock.advanceTo(55.millis)
              t <- expectNext(t, 50)
              _ <- expectNil(t)
            } yield ()
          }
      },

      "endless fibonacci" -> {
        val next: Val[(Int, Int)] -⚬ (Val[Int] |*| Val[(Int, Int)]) =
          id[Val[(Int, Int)]] > mapVal { case (n0, n1) => (n0, (n1, n0 + n1)) } > liftPair

        val fibonacci: Done -⚬ (Endless[Val[Int]] |*| Done) =
          constVal((0, 1)) > Endless.unfold(next) > par(id, neglect)

        def take[A](n: Int): Endless[Val[A]] -⚬ Val[List[A]] =
          Endless.take(n) > toScalaList

        val expected =
          List(0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181)

        TestCase.multiple(
          "take 20" ->
            TestCase
              .awaitVal { fibonacci > par(take(20), id) > awaitPosSnd }
              .checkThat { assertEquals(_, expected) },
          "split & take 10 from each" ->
            TestCase.interactWith[Val[(List[Int], List[Int])]] {
              fibonacci > par(Endless.split > par(take(10), take(10)) > unliftPair, id) > awaitPosSnd
            }.via { port =>
              for {
                results <- port.expectVal
                (fibs1, fibs2) = results
                _ <- Outcome.assert(fibs1.sorted == fibs1)
                _ <- Outcome.assert(fibs2.sorted == fibs2)
                _ <- Outcome.assert((fibs1 ++ fibs2).sorted == expected)
              } yield ()
            },
        )
      },

      "pool" -> {
        case class ClientId(value: Int)
        case class ResourceId(value: Int)

        val nResources = 3
        val nClients = 12

        def client(cid: ClientId): (Val[ResourceId] |*| Neg[ResourceId]) -⚬ Val[(ClientId, ResourceId)] =
          id                             [                            Val[ResourceId]             |*| Neg[ResourceId]  ]
            .>(fst(delayVal(1.milli))).to[                            Val[ResourceId]             |*| Neg[ResourceId]  ]
            .>(fst(dup).>(assocLR))   .to[                   Val[ResourceId] |*| (Val[ResourceId] |*| Neg[ResourceId]) ]
            .>(elimSnd(fulfill))      .to[                   Val[ResourceId]                                           ]
            .>(introFst(const(cid)))  .to[ Val[ClientId] |*| Val[ResourceId]                                           ]
            .>(unliftPair)            .to[ Val[(ClientId, ResourceId)]                                                 ]

        val clients: List[(Val[ResourceId] |*| Neg[ResourceId]) -⚬ Val[(ClientId, ResourceId)]] =
          (1 to nClients)
            .map { i => client(ClientId(i)) }
            .toList

        val clientsPrg: Unlimited[Val[ResourceId] |*| Neg[ResourceId]] -⚬ Val[List[(ClientId, ResourceId)]] =
          LList.fromListU(clients) > toScalaList

        val resources: Done -⚬ LList1[Val[ResourceId]] =
          LList1.from(
            head = constVal(ResourceId(1)),
            tail = (2 to nResources)
              .map { i => constVal(ResourceId(i)) }
              .toList,
          )

        val prg: Done -⚬ Val[List[(ClientId, ResourceId)]] =
          resources > Unlimited.poolBy(promise) > par(clientsPrg, LList1.foldMap(neglect)) > awaitPosSnd

        TestCase
          .interactWith(prg)
          .via { port =>
            for {
              pairs <- port.expectVal

              // each client appears exactly once
              _ <- Outcome.assert(pairs.size == nClients)
              _ <- Outcome.assert(pairs.map(_._1).toSet.size == nClients)

              // each resource is used by multiple clients
              _ <- Outcome.traverse(
                      pairs.groupMapReduce(key = _._2)(_ => 1)(_ + _)
                    ) { case (rId, n) =>
                      Outcome.assert(n >= nClients / nResources / 2, s"unbalanced resource usage: $pairs")
                    }
            } yield ()
          }
      },

      "LeasePool" -> {
        val LeaseCount = 5
        val ClientCount = 100
        TestCase.interactWith {
          val prg: Done -⚬ Val[List[Int]] =
            λ { case +(start) =>
              type Counter = Val[AtomicInteger]

              val pool: $[LeasePool] = LeasePool.fromList(LList1.fill(LeaseCount)(id[Done])(start))
              val counter: $[Counter] = constVal(new AtomicInteger(0))(start)
              val counters: $[LList1[Counter]] = LList1.fill(ClientCount)(id)(counter)
              val (pool1 |*| lease_counters) = (pool |*| counters) |> LList1.mapS(
                λ { case pool |*| cntr =>
                  val (lease |*| pool1) = LeasePool.acquireLease(pool)
                  pool1 |*| (lease |*| cntr)
                }
              )
              // Increments the counter when lease is obtained, decrements it before release.
              // Retrns the value of the counter after increment.
              val client: (Lease |*| Counter) -⚬ Val[Int] =
                λ { case lease |*| counter =>
                  Lease.notifyAcquired(lease) match
                    case ping |*| lease =>
                      val (counter1 ** n) = (counter deferUntil ping) |> mapVal(n => (n, n.incrementAndGet()))
                      val decremented = counter1 |> signalPosFst |> fst(delay(5.millis)) |> awaitPosFst |> mapVal(_.decrementAndGet) |> neglect
                      n alsoElim (Lease.releaseBy(decremented |*| lease))
                }
              val res: $[Val[List[Int]]] =
                lease_counters |> LList1.map(client) |> LList1.toLList |> toScalaList
              res waitFor LeasePool.close(pool1)
            }
          prg
        }
        .via { port =>
          for {
            ns <- port.expectVal
            _  <- Outcome.assert(ns.size == ClientCount, s"${ns.size} != $ClientCount")
            _  <- Outcome.assert(ns.forall(_ <= LeaseCount), s"contains values greater than $LeaseCount: ${ns.filter(_ >= LeaseCount)}")
            _  <- Outcome.assert(ns.contains(LeaseCount), s"Number of granted leases hasn't reached the full capacity of $LeaseCount. Maximum reached was ${ns.max}: $ns")
          } yield ()
        }
      },

      "backvert then forevert" -> TestCase.awaitVal {
        val prg: Done -⚬ Val[String] =
          constVal("abc") > introSnd(forevert[Val[String]]) > assocRL > elimFst(backvert[Val[String]])

        prg
      }.checkThat {
        assertEquals(_, "abc")
      },

      "distributeInversion, factorOutInversion" -> TestCase.awaitVal {
        val prg: Done -⚬ Val[(String, Int)] =
          fork > par(constVal("1") > dii, constVal(1) > dii) > factorOutInversion > contrapositive(distributeInversion) > die > unliftPair

        prg
      }.checkThat {
        assertEquals(_, ("1", 1))
      },

      "demandTogether > demandSeparately = id" -> TestCase.awaitDone {
        // namely, check that demandTogether does not delay processing until both demands are supplied

        val joinThenSplitDemands: (-[Done] |*| -[Done]) -⚬ (-[Done] |*| -[Done]) =
          demandTogether > demandSeparately

        val prg: Done -⚬ Done =
          λ { start =>
            val ((start1 |*| (nDone1 |*| done1)) |*| (nDone2 |*| done2)) =
              start
                .also(demand[Done])
                .also(demand[Done])

            val (nDone3 |*| nDone4) = joinThenSplitDemands(nDone1 |*| nDone2)

            done2
              .alsoElim(supply(start1 |*| nDone3))
              .alsoElim(supply(done1 |*| nDone4))
          }

        prg
      },

      "notifyChoice in reverse" -> TestCase.awaitVal {
        def notifyInvChoice[A, B]: -[A |&| B] -⚬ (Ping |*| -[A |&| B]) =
          contrapositive(notifyChoice) > demandSeparately > fst(invertedPongAsPing)

        val prg: Done -⚬ Val[Int] =
          λ { start =>
            val (start1 |*| (demand1 |*| offer1)) =
              start.also(demand[Val[String] |&| Val[Int]])

            val (ping |*| demand2) =
              demand1 |> notifyInvChoice

            val one: $[One] =
              (start1 |*| demandChosen(demand2)) |> |+|.switchWithL(
                caseLeft  = λ { case (start1 |*| strDemand) => supply(constVal("x")(start1) |*| strDemand) },
                caseRight = λ { case (start1 |*| intDemand) => supply(constVal(100)(start1) |*| intDemand) },
              )

            val res: $[Val[Int]] =
              offer1 |> chooseR

            ((ping |*| res) |> awaitPingFst)
              .alsoElim(one)
          }

        prg
      }.checkThat {
        assertEquals(_, 100)
      },

      "unContrapositive" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          unContrapositive(id[-[Done]])

        prg
      },

      "demandChosen" -> TestCase.awaitVal {
        val supplyChosen: -[Val[String] |&| Val[Int]] -⚬ -[Done] =
          demandChosen > either(
            contrapositive(constVal("foo")),
            contrapositive(constVal(42)),
          )

        val prg: Done -⚬ Val[Int] =
          introSnd(demand[Val[String] |&| Val[Int]] > par(supplyChosen, chooseR)) > assocRL > elimFst(supply)

        prg
      }.checkThat {
        assertEquals(_, 42)
      },

      "doneAsInvertedNeed" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          doneAsInvertedNeed > invertedNeedAsDone

        prg
      },

      "pingAsInvertedPong" -> TestCase.awaitDone {
        val f: Ping -⚬ Ping =
          pingAsInvertedPong > invertedPongAsPing

        val prg: Done -⚬ Done =
          notifyDoneL > fst(f) > awaitPingFst

        prg
      },

      "needAsInvertedDone" -> TestCase.awaitDone {
        val f: Need -⚬ Need =
          needAsInvertedDone > invertedDoneAsNeed

        val prg: Done -⚬ Done =
          introSnd(lInvertSignal > fst(f)) > assocRL > elimFst(rInvertSignal)

        prg
      },

      "pongAsInvertedPing" -> TestCase.awaitDone {
        val f: Pong -⚬ Pong =
          pongAsInvertedPing > invertedPingAsPong

        val g: Ping -⚬ Ping =
          introSnd(lInvertPongPing > fst(f)) > assocRL > elimFst(rInvertPingPong)

        val prg: Done -⚬ Done =
          notifyDoneL > fst(g) > awaitPingFst

        prg
      },

      "triple inversion" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          λ { d =>
            val (d1 |*| (nnd |*| nd)) = d.also(demand[-[Done]])
            val (nnnd |*| nnd2) = supply(d1 |*| nd) |> demand[-[-[Done]]]
            die(nnd2)
              .alsoElim(supply(nnd |*| nnnd))
          }

        prg
      },

      "on the demand side, demandSeparately, then supply one to the other" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          λ { d =>
            val (d1 |*| ((n_nd_d: $[-[-[Done] |*| Done]]) |*| (nd |*| d2))) =
              d.also(demand[-[Done] |*| Done])

            val (nnd |*| nd1) = demandSeparately(n_nd_d)

            d2
              .alsoElim(supply(nd1 |*| nnd))
              .alsoElim(supply(d1 |*| nd))
          }

        prg
      },

      "Lock: successful acquire and release" -> TestCase
        .interactWith {
          val prg: Done -⚬ (Done |+| Lock) =
            Lock.newLock > Lock.tryAcquire > |+|.lmap(AcquiredLock.release > Lock.close)

          prg
        }
        .via { _.expectLeft flatMap (_.expectDone) },

      "Lock: only 1 client can acquire at a time" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          λ { start =>
            val (lLock |*| rLock) =
              start |> Lock.newLock |> Lock.share

            // one lock can be acquired
            val (acquiredRLock |*| acquiredRNotification) =
              Lock.tryAcquire(rLock) |> leftOrCrash() |> notifyPosSnd

            // second acquisition attempt fails
            val (lLock1 |*| pingOnAttempted) =
              (lLock blockUntil acquiredRNotification) |> Lock.tryAcquire |> notifyPosSnd |> fst(rightOrCrash())

            // release the acquired lock, but only after the second acquisition attempt
            val rLock1 =
              AcquiredLock.release(acquiredRLock deferReleaseUntil pingOnAttempted)

            join( Lock.close(lLock1) |*| Lock.close(rLock1) )
          }

        prg
      },

      "Lock: Everyone acquires the lock eventually" -> TestCase.awaitDone {
        val prg: Done -⚬ Done =
          Lock.newLock > Lock.share > par(
            Lock.share > par(
              Lock.acquire > AcquiredLock.release > Lock.close,
              Lock.acquire > AcquiredLock.release > Lock.close,
            ),
            Lock.share > par(
              Lock.acquire > AcquiredLock.release > Lock.close,
              Lock.acquire > AcquiredLock.release > Lock.close,
            ),
          ) > joinMap(join, join)

        prg
      },

      "latestValue" ->
        TestCase.interactWith {
          val prg: Done -⚬ ((-[LList1[Val[Int]]] |*| Endless[Val[Int]]) |*| Done) =
            λ { d =>
              val nis |*| is = constant(demand[LList1[Val[Int]]])
              val out |*| d1 = latestValue(LList1.uncons(is))
              (nis |*| out) |*| join(d |*| d1)
            }
          prg
        }
        .via { port =>
          val N = 100
          val (snkSrc, d) = port.unzip()
          val (snk, src)  = snkSrc.unzip()

          // write numbers 0..N-1 at maximum speed
          val input: One -⚬ LList1[Val[Int]] =
            done > constList1(0, List.range(1, N))
          snk
            .append(λ { nis => constant(input) supplyTo nis })
            .discardOne()

          // read N numbers at maximum speed
          val out = bridge.append(src)(Endless.take(N) > toScalaList)

          // check that at least N/2 values were equal to the last written value (N-1)
          for {
            is <- out.expectVal
            _  <- Outcome.assert(is.count(_ == N-1) >= N/2, s"Expected ${N/2}+ values to be ${N-1}, got $is")
          } yield ()
        },

      "shared code" -> TestCase.awaitDone {
        val sharedPart: Done -⚬ Done =
          sharedCode(fork > swap > join)

        fork > par(sharedPart, sharedPart) > join
      },
    )
  }
}
