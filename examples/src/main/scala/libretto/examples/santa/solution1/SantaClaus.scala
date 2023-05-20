package libretto.examples.santa.solution1

import libretto.scaletto.StarterApp
import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams.Source
import scala.util.Random
import scala.concurrent.duration._
import scala.{:: => NonEmptyList}

object SantaClaus extends StarterApp {
  import scalettoLib.closeableCosemigroupVal
  import Monoid.monoidOne

  opaque type Reindeer = Val[String]
  opaque type Elf      = Val[String]

  def randomDelay(minMs: Int, maxMs: Int): Done -⚬ Done =
    constVal(()) > mapVal(_ => Random.between(minMs, maxMs).millis) > delay

  def vacation: Reindeer -⚬ Reindeer = λ { rndr =>
    rndr :>> alsoPrintLine(r => s"$r going on vacation")
         :>> delayVal(randomDelay(100, 200))
         :>> alsoPrintLine(r => s"$r returned from vacation")
  }

  def makeToys: Elf -⚬ Elf = λ { elf =>
    elf :>> alsoPrintLine(e => s"$e making toys")
        :>> delayVal(randomDelay(30, 50))
        :>> alsoPrintLine(e => s"$e needs consultation")
  }

  class Group[A](
    getName: A -⚬ (Val[String] |*| A),
    formatMessage: NonEmptyList[String] => String,
    onRelease: A -⚬ A,
  )(using SignalingJunction.Positive[A]) {
    opaque type Type = LList1[A |*| -[A]]

    def make: LList1[A |*| -[A]] -⚬ Type = id

    def act: Type -⚬ Done =
      collectNames > λ { case names |*| grp =>
        val +(done) = names :>> printLine(formatMessage) :>> randomDelay(50, 100)
        done alsoElim releaseWhen(done |*| grp)
      }

    private def releaseWhen: (Done |*| Type) -⚬ One =
      LList1.transform(assocRL > fst(awaitPosFst[A] > onRelease) > supply) > LList1.fold

    private def collectNames: Type -⚬ (Val[NonEmptyList[String]] |*| Type) =
      LList1.unzipBy(fst(getName) > assocLR) > fst(toScalaList1)

    given Affine[Type] =
      Affine.from(LList1.foldMap(supply))

    given Signaling.Positive[Type] =
      Signaling.Positive.from(LList1.unzipBy(fst(notifyPosFst[A]) > assocLR) > fst(LList1.fold))
  }

  val ReindeerGroup = Group[Reindeer](dup, names => s"Delivering toys with ${names.mkString(", ")}", vacation)
  val ElfGroup      = Group[Elf]     (dup, names => s"Meeting in study with ${names.mkString(", ")}", makeToys)

  type ReindeerGroup = ReindeerGroup.Type
  type ElfGroup = ElfGroup.Type

  def santa(nCycles: Int): Endless[ReindeerGroup |+| ElfGroup] -⚬ Done = {
    def go: (ReindeerGroup |+| ElfGroup) -⚬ Done =
      either(ReindeerGroup.act, ElfGroup.act)

    Endless.mapSequentially(go) > Endless.take(nCycles) > LList.fold
  }

  override def blueprint: Done -⚬ Done =
    λ.+ { start =>
      val reindeers = start :>> constList1Of("R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9")
      val elves     = start :>> constList1Of("E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9", "E10")
      val rGrpPool |*| releasedReindeers = reindeers :>> poolEndless :>> fst(Endless.groups(9) > Endless.map(ReindeerGroup.make))
      val eGrpPool |*| releasedElves     = elves     :>> poolEndless :>> fst(Endless.groups(3) > Endless.map(ElfGroup.make))
      santa(nCycles = 20)(Endless.mergeEitherPreferred[ReindeerGroup, ElfGroup](rGrpPool |*| eGrpPool))
        .waitFor(LList1.closeAll(releasedReindeers))
        .waitFor(LList1.closeAll(releasedElves))
    }
}
