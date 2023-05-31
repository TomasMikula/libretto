package libretto.examples.santa.solution1

import libretto.scaletto.StarterApp
import libretto.scaletto.StarterKit.{_, given}
import libretto.scaletto.StarterKit.Endless.{groupMap, mapSequentially, mergeEitherPreferred, take}
import libretto.scaletto.StarterKit.LList1.{closeAll, map}
import libretto.scaletto.StarterKit.Monoid.monoidOne
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

  class Group[A](
    getName: A -⚬ (Val[String] |*| A),
    formatMessage: NonEmptyList[String] => String,
  )(using SignalingJunction.Positive[A]) {
    import LList1.{fold, foldMap, transform, unzipBy}

    opaque type Type = LList1[A |*| -[A]]

    def make: LList1[A |*| -[A]] -⚬ Type = id

    def act: Type -⚬ Done =
      collectNames > λ { case names |*| grp =>
        val +(done) = names :>> printLine(formatMessage) :>> delayRandomMs(50, 100)
        returning(done, releaseWhen(done |*| grp))
      }

    private def releaseWhen: (Done |*| Type) -⚬ One =
      transform(assocRL > fst(awaitPosFst[A]) > supply) > fold

    private def collectNames: Type -⚬ (Val[NonEmptyList[String]] |*| Type) =
      unzipBy(fst(getName) > assocLR) > fst(toScalaList1)

    given Affine[Type] =
      Affine.from(foldMap(supply))

    given Signaling.Positive[Type] =
      Signaling.Positive.from(unzipBy(fst(notifyPosFst[A]) > assocLR) > fst(fold))
  }

  val ReindeerGroup = Group[Reindeer](dup, names => s"Delivering toys with ${names.mkString(", ")}")
  val ElfGroup      = Group[Elf]     (dup, names => s"Meeting in study with ${names.mkString(", ")}")

  type ReindeerGroup = ReindeerGroup.Type
  type ElfGroup = ElfGroup.Type

  def santa(nCycles: Int): Endless[ReindeerGroup |+| ElfGroup] -⚬ Done = {
    def go: (ReindeerGroup |+| ElfGroup) -⚬ Done =
      either(ReindeerGroup.act, ElfGroup.act)

    mapSequentially(go) > take(nCycles) > LList.fold
  }

  override def blueprint: Done -⚬ Done =
    λ.+ { start =>
      val reindeers : $[LList1[Reindeer]] = start :>> constList1Of("R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9")
      val elves     : $[LList1[Elf]]      = start :>> constList1Of("E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9", "E10")
      val rGroups |*| releasedReindeers = reindeers :>> map(vacation) :>> Endless.poolReset(vacation) :>> fst(groupMap(9, ReindeerGroup.make))
      val eGroups |*| releasedElves     = elves     :>> map(makeToys) :>> Endless.poolReset(makeToys) :>> fst(groupMap(3, ElfGroup.make))
      val groups: $[Endless[ReindeerGroup |+| ElfGroup]] = mergeEitherPreferred[ReindeerGroup, ElfGroup](rGroups |*| eGroups)
      joinAll(
        groups :>> santa(nCycles = 20),
        closeAll(releasedReindeers),
        closeAll(releasedElves),
      )
    }
}
