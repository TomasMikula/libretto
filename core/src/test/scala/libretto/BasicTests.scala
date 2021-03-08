package libretto

import java.util.concurrent.{Executors, ScheduledExecutorService}
import scala.collection.mutable
import scala.concurrent.{Await, Promise}
import scala.concurrent.duration._

class BasicTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.scalaLib._

  private var scheduler: ScheduledExecutorService = _

  override def beforeAll(): Unit = {
    super.beforeAll()
    scheduler = Executors.newScheduledThreadPool(2)
  }

  override def afterAll(): Unit = {
    scheduler.shutdown()
    super.afterAll()
  }

  private def delayedAsync[A](d: FiniteDuration)(a: => A): Async[A] = {
    val p = Promise[A]()
    scheduler.schedule({ () => p.success(a) }: Runnable, d.length, d.unit)
    Async.fromFuture(p.future).map(_.get)
  }

  private def raceKeepWinner[A](
    prg1: One -⚬ Val[A],
    prg2: One -⚬ Val[A],
  ): One -⚬ Val[A] =
    parFromOne(prg1, prg2)
      .race(
        caseFstWins = id.awaitSnd(neglect),
        caseSndWins = id.awaitFst(neglect),
      )

  test("done") {
    assertCompletes(done)
  }

  test("join ⚬ fork") {
    assertCompletes(done >>> fork >>> join)
  }

  test("constVal") {
    assertVal(done >>> constVal(5), 5)
  }

  test("unliftEither") {
    assertVal(const(42) >>> injectR >>> unliftEither, Right(42))
  }

  test("liftPair, liftNegPair") {
    val prg: One -⚬ Val[(String, Int)] =
      id                                       [       One                                                                            ]
        .>(const(("foo", 42)))              .to[     Val[(String, Int)]                                                               ]
        .introSnd(promise)                  .to[     Val[(String, Int)]      |*| (   Neg[(String, Int)]       |*| Val[(String, Int)]) ]
        .assocRL                            .to[ (   Val[(String, Int)]      |*|     Neg[(String, Int)]     ) |*| Val[(String, Int)]  ]
        .>.fst(par(liftPair, liftNegPair))  .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| Val[(String, Int)]  ]
        .>.fst(rInvert).elimFst             .to[                                                                  Val[(String, Int)]  ]

    assertVal(prg, ("foo", 42))
  }

  test("unliftPair, unliftNegPair") {
    val lInvert: One -⚬ ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) =
      coreLib.lInvert

    val prg: One -⚬ Val[(String, Int)] =
      id                                           [               One                                                                            ]
        .>(parFromOne(const("foo"), const(42))) .to[   Val[String] |*| Val[Int]                                                                   ]
        .introSnd.>.snd(lInvert)                .to[  (Val[String] |*| Val[Int]) |*| ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) ]
        .assocRL                                .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| (Val[String] |*| Val[Int])  ]
        .>.fst(par(unliftPair, unliftNegPair))  .to[ (    Val[(String, Int)]     |*|      Neg[(String, Int)]    ) |*| (Val[String] |*| Val[Int])  ]
        .elimFst(fulfill)                       .to[                                                                   Val[String] |*| Val[Int]   ]
        .>(unliftPair)                          .to[                                                                      Val[(String, Int)]      ]

    assertVal(prg, ("foo", 42))
  }

  test("inflate") {
    val prg: One -⚬ Done =
      id                                 [    One                            ]
        .>(const(42))                 .to[  Val[Int]                         ]
        .>(introSnd(lInvertSignal))   .to[  Val[Int] |*| ( Need    |*| Done) ]
        .assocRL                      .to[ (Val[Int] |*|   Need  ) |*| Done  ]
        .>.fst.snd(inflate)           .to[ (Val[Int] |*| Neg[Int]) |*| Done  ]
        .elimFst(fulfill)             .to[                             Done  ]

    assertCompletes(prg)
  }

  test("delayed injectL") {
    // 'A' delayed by 40 millis
    val a: One -⚬ Val[Char] =
      done >>> delay(40.millis) >>> constVal('A')

    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed inject (joinInjectL).
    val b: One -⚬ Val[Char] = {
      val delayedInjectL: One -⚬ (Val[Char] |+| Val[Char]) =
        done >>> fork(delay(30.millis), constVal('B')) >>> awaitInjectL
      delayedInjectL >>> either(
        introFst[Val[Char], Done](done >>> delay(20.millis)).awaitFst,
        id,
      )
    }

    assertVal(raceKeepWinner(a, b), 'A')
  }

  test("delayed chooseL") {
    // 'A' delayed by 40 millis
    val a: One -⚬ Val[Char] =
      done >>> delay(40.millis) >>> constVal('A')

    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed choice is made.
    val b: One -⚬ Val[Char] =
      done >>> fork(delay(30.millis), choice(delay(20.millis), id)) >>> awaitPosChooseL >>> constVal('B')

    assertVal(raceKeepWinner(a, b), 'A')
  }

  test("crash") {
    assertCrashes(done >>> crashd("boom!"), "boom!")
  }

  test("crash waits for its trigger") {
    val x = new java.util.concurrent.atomic.AtomicBoolean(false)

    val eff: Unit => Unit =
      _ => x.set(true)

    def prg(delayCrash: Boolean): One -⚬ Done = {
      val beforeCrash: Done -⚬ Done =
        if (delayCrash) delay(10.millis) else id

      done
        .>( fork )
        .par( beforeCrash     , delay(5.millis) )
        .par( crashd("Boom!"),  constVal(())    )
        .>( race )
        .>.right.snd(mapVal(eff))
        .either(id, id)
        .>.snd(neglect)
        .>(join)
    }

    assertCrashes(prg(delayCrash = false), "Boom!")
    assert(x.get() == false) // if the crash is not delayed, it wins the race and there's no effect

    assertCrashes(prg(delayCrash = true), "Boom!")
    assert(x.get() == true) // if the crash is delayed, there's time for the effect
  }

  test("crash - even if it loses a race, the program still crashes") {
    val prg = done
      .>>>( fork(id, delay(10.millis) >>> crashd("oops")) )
      .>>>( raceDone )
      .>>>( either(id, id) )
    assertCrashes(prg, "oops")
  }

  test("crash in non-executed |+| has no effect") {
    val prg = done
      .injectL[Done]
      .either(id, crashd("bang!"))
    assertCompletes(prg)
  }

  test("crash in non-chosen |&| alternative has no effect") {
    val prg = done
      .choice(id, crashd("bang!"))
      .chooseL
    assertCompletes(prg)
  }

  test("coDistribute") {
    type B = Val[Boolean]
    type C = Val[Char]
    type I = Val[Int]
    type S = Val[String]

    //               (false   1)    (true "foo")    ('a'    2)    ('b'  "bar")
    val init: One -⚬ (((B |*| I) |&| (B |*| S)) |&| ((C |*| I) |&| (C |*| S))) =
      choice(
        choice(
          parFromOne(const(false), const(1)),
          parFromOne(const(true), const("foo")),
        ),
        choice(
          parFromOne(const('a'), const(2)),
          parFromOne(const('b'), const("bar")),
        ),
      )

    val coDistributed1: One -⚬ ((B |&| C) |*| (I |&| S)) =
      init
        .bimap(coDistributeL, coDistributeL)
        .>(coDistributeR)

    val coDistributed2: One -⚬ ((B |&| C) |*| (I |&| S)) =
      init                                          .to[ ((B |*| I) |&| (B  |*|  S)) |&| ((C |*| I) |&| (C  |*| S)) ]
        .>(|&|.IXI)                                 .to[ ((B |*| I) |&| (C  |*|  I)) |&| ((B |*| S) |&| (C  |*| S)) ]
        .bimap(coDistributeR, coDistributeR)        .to[ ((B        |&|  C) |*|  I ) |&| ((B        |&|  C) |*| S ) ]
        .>(coDistributeL)                           .to[  (B        |&|  C) |*| (I   |&|                        S ) ]

    case class Combination[X, Y](
      choose1: (B |&| C) -⚬ Val[X],
      choose2: (I |&| S) -⚬ Val[Y],
      expectedX: X,
      expectedY: Y,
    ) {
      type T = X
      type U = Y

      def go: ((B |&| C) |*| (I |&| S)) -⚬ Val[(T, U)] =
        par(choose1, choose2) >>> unliftPair

      def expected: (T, U) =
        (expectedX, expectedY)
    }

    val combinations = Seq(
      Combination(chooseL, chooseL, false, 1),
      Combination(chooseL, chooseR, true, "foo"),
      Combination(chooseR, chooseL, 'a', 2),
      Combination(chooseR, chooseR, 'b', "bar"),
    )

    for {
      f <- Seq(coDistributed1, coDistributed2)
      c <- combinations
    } {
      assertVal(f >>> c.go, c.expected)
    }
  }

  test("LList.splitEvenOdd") {
    val prg: One -⚬ Val[(List[Int], List[Int])] =
      constListOf((0 to 100): _*) > LList.splitEvenOdd > par(toScalaList, toScalaList) > unliftPair

    assertVal(prg, (0 to 100).toList.partition(_ % 2 == 0))
  }

  test("LList.halfRotateL") {
    val prg: One -⚬ Val[List[(Int, Int)]] =
      constList(List((0, 1), (2, 3), (4, 5)))
        .>(LList.map(liftPair))
        .>(LList.halfRotateL)
        .>(LList.map(unliftPair))
        .>(toScalaList)

    assertVal(prg, List((1, 2), (3, 4), (5, 0)))
  }

  test("acquire - effect - transform - release") {
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

    val prgs: Seq[One -⚬ Val[String]] = {
      for {
        acquireMVar <- acquireFuns
        incMVar <- incFuns
        mvarToString <- toStringTrans
        releaseMVar <- releaseFuns
      } yield {
        const(0)
          .>(acquireMVar)
          .>(incMVar)
          .>(mvarToString)
          .>(releaseMVar)
      }
    }

    for (prg <- prgs) {
      assertVal(prg, "1")
    }
  }

  test("release via registered function") {
    val ref = new java.util.concurrent.atomic.AtomicReference[String]("init")

    val prg: One -⚬ Done =
      const(()) > acquire0(identity, release = Some(_ => ref.set("released"))) > release

    assertCompletes(prg)
    assert(ref.get() == "released")
  }

  test("splitResource") {
    val store = new java.util.concurrent.atomic.AtomicReference[List[String]](Nil)

    def log(s: String): Unit =
      store.updateAndGet(s :: _)

    val prg: One -⚬ Done =
      const(())
        .>(acquire0[Unit, Unit](
          acquire = _ => log("acquire A"),
          release = Some(_ => log("release A")), // this release function should never be invoked
        ))
        .>(splitResource0(
          _ => { log("split A -> (B, C)"); ((), ()) },
          release1 = Some(_ => log("release B")),
          release2 = Some(_ => log("release C")),
        ))
        .par(release, release)
        .>(join)

    assertCompletes(prg)

    val logEntries: List[String] = store.get().reverse

    assert(logEntries.take(2) == List("acquire A", "split A -> (B, C)"))
    assert(logEntries.drop(2).toSet == Set("release B", "release C"))
    assert(logEntries.size == 4)
  }

  test("splitResourceAsync: check that resources are released if program crashes during their asynch acquisition") {
    val store = new java.util.concurrent.atomic.AtomicReference[List[String]](Nil)

    def log(s: String): Unit =
      store.updateAndGet(s :: _)

    val pb, pc = Promise[Unit]()

    val mainThread: One -⚬ Done =
      const(())
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
        .par(
          release0[Unit, Unit](_ => log("release B XXX")) > neglect, // this release function should never be invoked
          release0[Unit, Unit](_ => log("release C XXX")) > neglect, // this release function should never be invoked
        )
        .>(join)

    val crashThread: One -⚬ Done =
      done > delay(5.millis) > crashd("Boom!") // delay crash to give chance for resource split to begin

    val prg: One -⚬ Done =
      parFromOne(crashThread, mainThread) > join

    assertCrashes(prg, "Boom!")

    // The current implementation based on Futures does not guarantee that all processing has finished by the time
    // the program returns an error. Therefore, explicitly await completion of the release functions.
    Await.result(pb.future zip pc.future, 1.second)

    val logEntries: List[String] = store.get().reverse

    assert(logEntries.take(2) == List("acquire A", "split A -> (B, C)"))
    assert(logEntries.drop(2).toSet == Set("release B", "release C"))
    assert(logEntries.size == 4)
  }

  test("RefCounted") {
    import java.util.concurrent.atomic.AtomicInteger

    val releaseCounter = new AtomicInteger(0)
    val incGetClose: RefCounted[AtomicInteger] -⚬ Val[Int] =
      introSnd(const(()))                                       .to[ RefCounted[AtomicInteger] |*| Val[Unit] ]
        .>( RefCounted.effect((i, _) => i.incrementAndGet) )    .to[ RefCounted[AtomicInteger] |*| Val[Int]  ]
        .awaitFst(RefCounted.release)                           .to[                               Val[Int]  ]

    val prg: One -⚬ Val[Int] =
      const(0)
        .>(RefCounted.acquire0(new AtomicInteger(_), _ => releaseCounter.incrementAndGet))
        .>(RefCounted.dupRef)
        .>.snd(RefCounted.dupRef)
        .par(incGetClose, par(incGetClose, incGetClose))
        .>.snd(unliftPair > mapVal(t => t._1 + t._2))
        .>(unliftPair > mapVal(t => t._1 + t._2))

    assertVal(prg, 6)
    assert(releaseCounter.get() == 1)
  }

  test("blocking") {
    val n = 10
    val sleepMillis = 10

    case class Millis(value: Long)

    val currentTimeMillis: Done -⚬ Val[Millis] =
      constVal(()) > mapVal(_ => Millis(System.currentTimeMillis()))

    val sleep: Done -⚬ Val[Millis] =
      constVal(()) > blocking(_ => Thread.sleep(sleepMillis)) > mapVal(_ => Millis(System.currentTimeMillis()))

    val timed: One -⚬ Val[(List[Millis], List[Millis])] = {
      // true, false, true, false, ...
      val alternating: List[Boolean] = (0 until (2*n)).map(_ % 2 == 0).toList

      constList(alternating)
        .>(LList.map(liftBoolean))
        .>(LList.map(Bool.switch(caseTrue = sleep, caseFalse = currentTimeMillis)))
        .>(LList.splitEvenOdd)
        .>(par(toScalaList, toScalaList))
        .>(unliftPair)
    }

    val prg: One -⚬ Val[(Millis, (List[Millis], List[Millis]))] =
      parFromOne(done > currentTimeMillis, timed) > unliftPair

    testVal(prg) { case (startMillis, (sleepEnds, pureEnds)) =>
      val sleepDurations = sleepEnds.map(_.value - startMillis.value)
      val pureDurations = pureEnds.map(_.value - startMillis.value)

      // sanity check: check that the blocking computations take the amount of time they are supposed to
      assert(sleepDurations.min >= sleepMillis)

      // check that none of the non-blocking computations is blocked by any of the blocking computations,
      // by checking that it completed before any of the blocking computations could
      assert(pureDurations.max < sleepMillis)
    }
  }
}
