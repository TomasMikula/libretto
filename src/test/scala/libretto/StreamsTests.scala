package libretto

import scala.concurrent.duration._

class StreamsTests extends TestSuite {
  import kit.dsl._
  import kit.coreLib._
  import kit.coreStreams._
  import kit.scalaLib._
  
  val scalaStreams = ScalaStreams(kit.dsl, kit.coreLib, kit.scalaLib, kit.coreStreams)
  
  import scalaStreams._
  
  test("toList ⚬ fromList = id") {
    assertVal(
      Pollable.fromList(List(1, 2, 3, 4, 5, 6)) >>> Pollable.toList,
      List(1, 2, 3, 4, 5, 6),
    )
  }

  test("Pollable.map") {
    assertVal(
      Pollable.fromList(List(1, 2, 3)) >>> Pollable.map(_.toString) >>> Pollable.toList,
      List("1", "2", "3"),
    )
  }

  test("partition") {
    assertVal(
      Pollable.of(1, 2, 3, 4, 5, 6)
        .>>>(Pollable.map { i => if (i % 2 == 0) Left(i) else Right(i) })
        .>>>(Pollable.partition)
        .par(Pollable.toList, Pollable.toList)
        .>>>(unliftPair),
      (List(2, 4, 6), List(1, 3, 5)),
    )
  }

  test("concat") {
    assertVal(
      parFromOne(Pollable.of(1, 2, 3), Pollable.of(4, 5, 6))
        .>(Pollable.concat)
        .>(Pollable.toList),
      List(1, 2, 3 ,4, 5, 6),
    )
  }

  test("merge") {
    assertVal(
      parFromOne(
        Pollable.of(1, 2, 3),
        Pollable.of(4, 5, 6),
      )
        .>(Pollable.merge)
        .>(Pollable.toList)
        .>(liftV(_.toSet)),
      Set(1, 2, 3, 4, 5, 6),
    )
  }

  test("mergeAll") {
    testVal(
      LList
        .of(
          Pollable.of(1, 2, 3),
          Pollable.of(4, 5, 6) >>> Pollable.delay(10.millis),
          Pollable.of(7, 8, 9),
        )
        .>(Pollable.mergeAll)
        .>(Pollable.toList)
    ) { (res: List[Int]) =>
      assert(res.toSet == Set(1, 2, 3, 4, 5, 6, 7, 8, 9))
      val (res1, res2) = res.splitAt(6)
      assert(res1.toSet == Set(1, 2, 3, 7, 8, 9))
      assert(res2 == List(4, 5, 6))
    }
  }
  
  test("subscribeByKey") {
    import Pollable.subscribeByKey
    import LSubscriber._

    val byLength: Val[String] -⚬ (Val[Int] |*| Val[String]) =
      liftV[String, (Int, String)](s => (s.length, s)) >>> liftPair
      
    val input: One -⚬ Pollable[String] =
      Pollable.of("f", "fo", "foo", "fooo", "foooo", "pho", "phoo", "phooo", "bo", "boo")
      
    def subscription(k: Int): One -⚬ (Pollable[String] |*| (Val[Int] |*| Subscriber[String])) =
      id                                     [                  One                                   ]
        .>(lInvertPollable)               .to[ Pollable[String] |*|               Subscriber[String]  ]
        .>.snd(introFst(const_(k)))       .to[ Pollable[String] |*| (Val[Int] |*| Subscriber[String]) ]

    val subscriptions: One -⚬ (LList[Val[Int] |*| Subscriber[String]] |*| LList[Pollable[String]]) =
      LList.of(subscription(3), subscription(4)) >>> LList.unzip >>> swap

    val prg: One -⚬ Val[List[String]] =
      parFromOne(input, subscriptions)    .to[  Pollable[String] |*| (    LList[Val[Int] |*| Subscriber[String]]  |*| LList[Pollable[String]]) ]
        .>(|*|.assocRL)                   .to[ (Pollable[String] |*|      LList[Val[Int] |*| Subscriber[String]]) |*| LList[Pollable[String]]  ]
        .>.fst.snd(LPollable.fromLList)   .to[ (Pollable[String] |*|  LPollable[Val[Int] |*| Subscriber[String]]) |*| LList[Pollable[String]]  ]
        .>.fst(subscribeByKey(byLength))  .to[                   Done                                             |*| LList[Pollable[String]]  ]
        .>.snd(Pollable.mergeAll)         .to[                   Done                                             |*|       Pollable[String]   ]
        .>.snd(Pollable.toList)           .to[                   Done                                             |*|      Val[List[String]]   ]
        .>.joinL                          .to[                                                                             Val[List[String]]   ]
        
    assertVal(
      prg >>> liftV(_.toSet),
      Set("foo", "fooo", "pho", "phoo", "boo"),
    )
  }
}
