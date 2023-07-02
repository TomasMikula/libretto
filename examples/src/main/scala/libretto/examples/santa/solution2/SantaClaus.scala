package libretto.examples.santa.solution2

import libretto.scaletto.StarterApp
import libretto.scaletto.StarterKit.*
import libretto.stream.scaletto.DefaultStreams.Source
import scala.{:: => NonEmptyList}

object SantaClaus extends StarterApp {
  opaque type Reindeer = Val[String]
  opaque type Elf      = Val[String]

  def vacation: Reindeer -⚬ Reindeer = λ { rndr =>
    rndr :>> alsoPrintLine(r => s"$r going on vacation")
         :>> delayValRandomMs(100, 200)
         :>> alsoPrintLine(r => s"$r returned from vacation")
  }

  def makeToys: Elf -⚬ Elf = λ { elf =>
    elf :>> alsoPrintLine(e => s"$e making toys")
        :>> delayValRandomMs(30, 50)
        :>> alsoPrintLine(e => s"$e needs consultation")
  }

  opaque type ReindeerGroup = Val[NonEmptyList[String]]
  opaque type ElfGroup      = Val[NonEmptyList[String]]

  object ReindeerGroup {
    def make: LList1[Reindeer] -⚬ ReindeerGroup = toScalaList1
    def ungroup: ReindeerGroup -⚬ LList1[Reindeer] = liftScalaList1
    def notifyReady: ReindeerGroup -⚬ (Ping |*| ReindeerGroup) = notifyVal
  }

  object ElfGroup {
    def make: LList1[Elf] -⚬ ElfGroup = toScalaList1
    def ungroup: ElfGroup -⚬ LList1[Elf] = liftScalaList1
    def notifyReady: ElfGroup -⚬ (Ping |*| ElfGroup) = notifyVal
  }

  def santa: Source[ReindeerGroup |+| ElfGroup] -⚬ Source[ReindeerGroup |+| ElfGroup] = {
    def deliverToys: ReindeerGroup -⚬ ReindeerGroup = alsoPrintLine[NonEmptyList[String]](grp => s"Delivering toys with ${grp.mkString(", ")}") > delayValRandomMs(50, 100)
    def meetInStudy:      ElfGroup -⚬ ElfGroup      = alsoPrintLine[NonEmptyList[String]](grp => s"Meeting in study with ${grp.mkString(", ")}") > delayValRandomMs(10, 20)

    def go: (ReindeerGroup |+| ElfGroup) -⚬ (Ping |*| (ReindeerGroup |+| ElfGroup)) =
      either(
        deliverToys > ReindeerGroup.notifyReady > snd(injectL),
        meetInStudy > ElfGroup.notifyReady > snd(injectR),
      )

    Source.mapSequence(go)
  }

  def pipeline(nCycles: Int): (LList[Reindeer] |*| LList[Elf]) -⚬ ((LList[Reindeer] |*| LList[Elf]) |*| Done) =
    λ { case reindeers |*| elves =>
      val rGrps = reindeers :>> (LList.map(vacation) > LList.sortBySignal > Source.fromLList > Source.groups(9) > Source.map(ReindeerGroup.make))
      val eGrps = elves     :>> (LList.map(makeToys) > LList.sortBySignal > Source.fromLList > Source.groups(3) > Source.map(ElfGroup.make))
      val pings |*| outGrps = (rGrps |*| eGrps) :>> (Source.mergeEitherPreferred[ReindeerGroup, ElfGroup] > santa > Source.tapMap(notifyEither))
      val outRGs |*| outEGs = LList.partition(outGrps)
      val outRs = outRGs :>> LList.flatMap(ReindeerGroup.ungroup > LList1.toLList)
      val outEs = outEGs :>> LList.flatMap(ElfGroup.ungroup > LList1.toLList)
      (outRs |*| outEs) |*| (pings :>> Source.take(nCycles) :>> Source.drain)
    }

  def go(nCycles: Int): (LList[Reindeer] |*| LList[Elf]) -⚬ Done =
    λ { case reindeers |*| elves =>
      val promise |*| (returningReindeers |*| returningElves) = constant(demand[LList[Reindeer] |*| LList[Elf]])
      val rs = LList.concat(reindeers |*| returningReindeers)
      val es = LList.concat(elves |*| returningElves)
      val returningHelpers |*| done = pipeline(nCycles)(rs |*| es)
      done alsoElim supply(returningHelpers |*| promise)
    }

  override def blueprint: Done -⚬ Done =
    λ.+ { start =>
      val reindeers = start :>> constListOf1("R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9")
      val elves     = start :>> constListOf1("E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9", "E10")
      go(nCycles = 20)(reindeers |*| elves)
    }
}
