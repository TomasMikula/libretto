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
    prg1: Done -⚬ Val[A],
    prg2: Done -⚬ Val[A],
  ): Done -⚬ Val[A] =
    fork(prg1, prg2)
      .race(
        caseFstWins = id.awaitSnd(neglect),
        caseSndWins = id.awaitFst(neglect),
      )

  test("done") {
    assertCompletes(introFst(done) > join)
  }

  test("join ⚬ fork") {
    assertCompletes(fork > join)
  }

  test("constVal") {
    assertVal(constVal(5), 5)
  }

  test("unliftEither") {
    assertVal(constVal(42) > injectR > unliftEither, Right(42))
  }

  test("liftPair, liftNegPair") {
    val prg: Done -⚬ Val[(String, Int)] =
      id                                       [       Done                                                                           ]
        .>(constVal(("foo", 42)))           .to[     Val[(String, Int)]                                                               ]
        .introSnd(promise)                  .to[     Val[(String, Int)]      |*| (   Neg[(String, Int)]       |*| Val[(String, Int)]) ]
        .assocRL                            .to[ (   Val[(String, Int)]      |*|     Neg[(String, Int)]     ) |*| Val[(String, Int)]  ]
        .>.fst(par(liftPair, liftNegPair))  .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| Val[(String, Int)]  ]
        .>.fst(rInvert).elimFst             .to[                                                                  Val[(String, Int)]  ]

    assertVal(prg, ("foo", 42))
  }

  test("unliftPair, unliftNegPair") {
    val lInvert: One -⚬ ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) =
      coreLib.lInvert

    val prg: Done -⚬ Val[(String, Int)] =
      id                                           [               Done                                                                           ]
        .>(fork(constVal("foo"), constVal(42))) .to[   Val[String] |*| Val[Int]                                                                   ]
        .introSnd.>.snd(lInvert)                .to[  (Val[String] |*| Val[Int]) |*| ((Neg[String] |*| Neg[Int])  |*| (Val[String] |*| Val[Int])) ]
        .assocRL                                .to[ ((Val[String] |*| Val[Int]) |*|  (Neg[String] |*| Neg[Int])) |*| (Val[String] |*| Val[Int])  ]
        .>.fst(par(unliftPair, unliftNegPair))  .to[ (    Val[(String, Int)]     |*|      Neg[(String, Int)]    ) |*| (Val[String] |*| Val[Int])  ]
        .elimFst(fulfill)                       .to[                                                                   Val[String] |*| Val[Int]   ]
        .>(unliftPair)                          .to[                                                                      Val[(String, Int)]      ]

    assertVal(prg, ("foo", 42))
  }

  test("inflate") {
    val prg: Done -⚬ Done =
      id                                 [    Done                           ]
        .>(constVal(42))              .to[  Val[Int]                         ]
        .>(introSnd(lInvertSignal))   .to[  Val[Int] |*| ( Need    |*| Done) ]
        .assocRL                      .to[ (Val[Int] |*|   Need  ) |*| Done  ]
        .>.fst.snd(inflate)           .to[ (Val[Int] |*| Neg[Int]) |*| Done  ]
        .elimFst(fulfill)             .to[                             Done  ]

    assertCompletes(prg)
  }

  test("delayed injectL") {
    // 'A' delayed by 40 millis
    val a: Done -⚬ Val[Char] =
      delay(40.millis) > constVal('A')

    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed inject (joinInjectL).
    val b: Done -⚬ Val[Char] = {
      val delayedInjectL: Done -⚬ (Val[Char] |+| Val[Char]) =
        fork(delay(30.millis), constVal('B')) > awaitInjectL
      delayedInjectL > either(
        introFst[Val[Char], Done](done > delay(20.millis)).awaitFst,
        id,
      )
    }

    assertVal(raceKeepWinner(a, b), 'A')
  }

  test("delayed chooseL") {
    // 'A' delayed by 40 millis
    val a: Done -⚬ Val[Char] =
      delay(40.millis) > constVal('A')

    // 'B' delayed by 30 + 20 = 50 millis.
    // We are testing that the second timer starts ticking only after the delayed choice is made.
    val b: Done -⚬ Val[Char] =
      fork(delay(30.millis), choice(delay(20.millis), id)) > awaitPosChooseL > constVal('B')

    assertVal(raceKeepWinner(a, b), 'A')
  }

  test("crash") {
    assertCrashes(crashd("boom!"), "boom!")
  }

  test("crash waits for its trigger") {
    val x = new java.util.concurrent.atomic.AtomicBoolean(false)

    val eff: Unit => Unit =
      _ => x.set(true)

    def prg(delayCrash: Boolean): Done -⚬ Done = {
      val beforeCrash: Done -⚬ Done =
        if (delayCrash) delay(10.millis) else id

      fork
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
    val prg = id[Done]
      .>( fork(id, delay(10.millis) > crashd("oops")) )
      .>( raceDone )
      .>( either(id, id) )
    assertCrashes(prg, "oops")
  }

  test("crash in non-executed |+| has no effect") {
    val prg = injectL[Done, Done] > either(id, crashd("bang!"))
    assertCompletes(prg)
  }

  test("crash in non-chosen |&| alternative has no effect") {
    val prg = choice(id, crashd("bang!")) > chooseL
    assertCompletes(prg)
  }

  test("coDistribute") {
    type B = Val[Boolean]
    type C = Val[Char]
    type I = Val[Int]
    type S = Val[String]

    //                (false   1)    (true "foo")    ('a'    2)    ('b'  "bar")
    val init: Done -⚬ (((B |*| I) |&| (B |*| S)) |&| ((C |*| I) |&| (C |*| S))) =
      choice(
        choice(
          fork(constVal(false), constVal(1)),
          fork(constVal(true), constVal("foo")),
        ),
        choice(
          fork(constVal('a'), constVal(2)),
          fork(constVal('b'), constVal("bar")),
        ),
      )

    val coDistributed1: Done -⚬ ((B |&| C) |*| (I |&| S)) =
      init
        .bimap(coDistributeL, coDistributeL)
        .>(coDistributeR)

    val coDistributed2: Done -⚬ ((B |&| C) |*| (I |&| S)) =
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
        par(choose1, choose2) > unliftPair

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
      assertVal(f > c.go, c.expected)
    }
  }

  test("LList.splitEvenOdd") {
    val prg: Done -⚬ Val[(List[Int], List[Int])] =
      constList1Of(0, (1 to 100): _*) > LList1.toLList > LList.splitEvenOdd > par(toScalaList, toScalaList) > unliftPair

    assertVal(prg, (0 to 100).toList.partition(_ % 2 == 0))
  }

  test("LList.halfRotateL") {
    val prg: Done -⚬ Val[List[(Int, Int)]] =
      constList1Of((0, 1), (2, 3), (4, 5))
        .>(LList1.toLList)
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

    val prgs: Seq[Done -⚬ Val[String]] = {
      for {
        acquireMVar <- acquireFuns
        incMVar <- incFuns
        mvarToString <- toStringTrans
        releaseMVar <- releaseFuns
      } yield {
        constVal(0)
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

    val prg: Done -⚬ Done =
      constVal(()) > acquire0(identity, release = Some(_ => ref.set("released"))) > release

    assertCompletes(prg)
    assert(ref.get() == "released")
  }

  test("splitResource") {
    val store = new java.util.concurrent.atomic.AtomicReference[List[String]](Nil)

    def log(s: String): Unit =
      store.updateAndGet(s :: _)

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
        .par(
          release0[Unit, Unit](_ => log("release B XXX")) > neglect, // this release function should never be invoked
          release0[Unit, Unit](_ => log("release C XXX")) > neglect, // this release function should never be invoked
        )
        .>(join)

    val crashThread: Done -⚬ Done =
      delay(5.millis) > crashd("Boom!") // delay crash to give chance for resource split to begin

    val prg: Done -⚬ Done =
      fork(crashThread, mainThread) > join

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

    val prg: Done -⚬ Val[Int] =
      constVal(0)
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

    val timed: Done -⚬ Val[(List[Millis], List[Millis])] = {
      // true, false, true, false, ...
      val alternating: ::[Boolean] = (0 until (2*n)).map(_ % 2 == 0).toList.asInstanceOf[::[Boolean]]

      constList1(alternating)
        .>(LList1.toLList)
        .>(LList.map(liftBoolean))
        .>(LList.map(Bool.switch(caseTrue = sleep, caseFalse = currentTimeMillis)))
        .>(LList.splitEvenOdd)
        .>(par(toScalaList, toScalaList))
        .>(unliftPair)
    }

    val prg: Done -⚬ Val[(Millis, (List[Millis], List[Millis]))] =
      fork(currentTimeMillis, timed) > unliftPair

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

  test("LList.sortBySignal") {
    val delays =
      List(30, 20, 10, 50, 40)

    val elems: ::[Done -⚬ Val[Int]] =
      delays
        .map(n => delay(n.millis) > constVal(n))
        .asInstanceOf[::[Done -⚬ Val[Int]]]

    val prg: Done -⚬ Val[List[Int]] =
      id                               [       Done       ]
        .>(LList1.from(elems))      .to[ LList1[Val[Int]] ]
        .>(LList1.toLList)          .to[  LList[Val[Int]] ]
        .>(LList.sortBySignal)      .to[  LList[Val[Int]] ]
        .>(toScalaList)             .to[   Val[List[Int]] ]

    assertVal(prg, delays.sorted)
  }

  test("endless fibonacci") {
    val next: Val[(Int, Int)] -⚬ (Val[Int] |*| Val[(Int, Int)]) =
      id[Val[(Int, Int)]] > mapVal { case (n0, n1) => (n0, (n1, n0 + n1)) } > liftPair

    val fibonacci: Done -⚬ (Endless[Val[Int]] |*| Done) =
      constVal((0, 1)) > Endless.unfold(next) > par(id, neglect)

    def take[A](n: Int): Endless[Val[A]] -⚬ Val[List[A]] =
      Endless.take(n) > toScalaList

    val prg: Done -⚬ Val[List[Int]] =
      fibonacci > par(take(20), id) > awaitPosSnd

    val expected = List(0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987, 1597, 2584, 4181)

    assertVal(prg, expected)

    val prg2: Done -⚬ Val[(List[Int], List[Int])] =
      fibonacci > par(Endless.split > par(take(10), take(10)) > unliftPair, id) > awaitPosSnd

    testVal(prg2) { case (fibs1, fibs2) =>
      assert(fibs1.sorted == fibs1)
      assert(fibs2.sorted == fibs2)
      assert((fibs1 ++ fibs2).sorted == expected)
    }
  }

  test("pool") {
    case class ClientId(value: Int)
    case class ResourceId(value: Int)

    val nResources = 3
    val nClients = 12

    def client(cid: ClientId): (Val[ResourceId] |*| Neg[ResourceId]) -⚬ Val[(ClientId, ResourceId)] =
      id                             [                            Val[ResourceId]             |*| Neg[ResourceId]  ]
        .>.fst(dup).assocLR       .to[                   Val[ResourceId] |*| (Val[ResourceId] |*| Neg[ResourceId]) ]
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
      resources > pool(promise) > par(clientsPrg, LList1.foldMap(neglect)) > awaitPosSnd

    testVal(prg) { pairs =>
      // each client appears exactly once
      assert(pairs.size == nClients)
      assert(pairs.map(_._1).toSet.size == nClients)

      // each resource is used by multiple clients
      pairs.groupMapReduce(key = _._2)(_ => 1)(_ + _).foreach { case (rId, n) =>
        assert(n >= nClients / nResources / 2, s"unbalanced resource usage: $pairs")
      }
    }
  }
}
