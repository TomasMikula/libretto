package libretto.examples

import libretto.scaletto.StarterApp
import scala.concurrent.duration._

/**
 * N scientists sharing M microscopes (N > M).
 *
 * This examples demonstrates:
 *  - concurrency (scientists operate concurrently)
 *  - sequencing (each scientist performs experiments sequentially, at most one at a time)
 *  - resource sharing via pooling (the limited number of microscopes is made available throught a pool)
 */
object PoolingMicroscopes extends StarterApp {
  object Microscopes {
    case class Name(value: String)

    opaque type Microscope = Val[Name]
    type BorrowedMicroscope = Microscope |*| -[Microscope]

    def newMicroscope: Val[Name] -⚬ Microscope =
      id

    def destroyMicroscope: Microscope -⚬ Done =
      neglect

    object BorrowedMicroscope {
      def use(f: Val[Name] -⚬ Done): BorrowedMicroscope -⚬ Done =
        id[BorrowedMicroscope]              .to[         Val[Name]         |*| -[Val[Name]] ]
          .>(fst(dup))                      .to[ (Val[Name] |*| Val[Name]) |*| -[Val[Name]] ]
          .>(fst(fst(f)))                   .to[ (  Done    |*| Val[Name]) |*| -[Val[Name]] ]
          .>(fst(awaitPosFst))              .to[                Val[Name]  |*| -[Val[Name]] ]
          .>(fst(signalPosFst))             .to[ (  Done    |*| Val[Name]) |*| -[Val[Name]] ]
          .>(assocLR > elimSnd(backvert))   .to[    Done                                    ]
    }

    // signalMicroscopeReadiness
    given Signaling.Positive[Microscope] =
      signalingVal
  }
  import Microscopes._

  def doExperiment(
    scientistName: String,
    experimentName: String,
    experimentDuration: FiniteDuration,
  ): (Done |*| Unlimited[BorrowedMicroscope]) -⚬ (Done |*| Unlimited[BorrowedMicroscope]) = {
    def go: BorrowedMicroscope -⚬ Done = {
      def initMsg(microscopeName: Name): String =
        s"$scientistName starting $experimentName on ${microscopeName.value}"

      def doneMsg(microscopeName: Name): String =
        s"$scientistName finished $experimentName on ${microscopeName.value}"

      BorrowedMicroscope.use {
        alsoPrintLine(initMsg) > delayVal(experimentDuration) > printLine(doneMsg)
      }
    }

    Unlimited.getFstWhenDone > assocRL > fst(snd(go) > join)
  }

  def scientist(name: String, experiments: (String, FiniteDuration)*): Unlimited[BorrowedMicroscope] -⚬ Done = {
    def go: (Done |*| Unlimited[BorrowedMicroscope]) -⚬ (Done |*| Unlimited[BorrowedMicroscope]) =
      experiments.foldLeft(id)((f, exp) => f > doExperiment(name, exp._1, exp._2))

    introFst(done) > go > elimSnd(Unlimited.discard)
  }

  def scientists: List[Unlimited[BorrowedMicroscope] -⚬ Done] =
    List(
      scientist("Watson",
        "Experiment Wa1" -> 700.millis,
        "Experiment Wa2" -> 1100.millis,
        "Experiment Wa3" -> 900.millis,
      ),
      scientist("Crick",
        "Experiment Cr1" -> 1500.millis,
        "Experiment Cr2" -> 1300.millis,
        "Experiment Cr3" -> 1400.millis,
      ),
      scientist("Fleming",
        "Experiment Fl1" -> 1.second,
        "Experiment Fl2" -> 1500.millis,
        "Experiment Fl3" -> 1200.millis,
      ),
      scientist("Curie",
        "Experiment Cu1" -> 800.millis,
        "Experiment Cu2" -> 700.millis,
        "Experiment Cu3" -> 600.millis,
        "Experiment Cu4" -> 500.millis,
        "Experiment Cu5" -> 400.millis,
      ),
    )

  override def blueprint: Done -⚬ Done =
    id[Done]
      .>(createMicroscopes)
      .>(Unlimited.pool)
      .>(fst(LList.fromList(scientists)))
      .>(fst(LList.fold))
      .>(snd(destroyMicroscopes))
      .>(join)

  def createMicroscopes: Done -⚬ LList1[Microscope] =
    constList1Of(
      Name("Microscope A"),
      Name("Microscope B"),
    ) > LList1.map(newMicroscope)

  def destroyMicroscopes: LList1[Microscope] -⚬ Done =
    LList1.foldMap(destroyMicroscope)
}
