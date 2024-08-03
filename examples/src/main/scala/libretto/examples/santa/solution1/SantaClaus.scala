package libretto.examples.santa.solution1

import libretto.scaletto.StarterApp
import libretto.scaletto.StarterKit.{*, given}
import libretto.scaletto.StarterKit.Endless.{groupMap, mapSequentially, mergeEitherPreferred, take}
import libretto.scaletto.StarterKit.LList1.{closeAll, eachNotifyBy, foldMap, map, sortBySignal, transform, unzipBy}
import libretto.scaletto.StarterKit.Monoid.given
import scala.{:: as NonEmptyList}

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
    getName   : A -⚬ (Val[String] |*| A),
    formatMsg : NonEmptyList[String] => String,
  )(using
    SignalingJunction.Positive[A],
  ) {
    opaque type Type = LList1[A |*| -[A]]

    def make: LList1[A |*| -[A]] -⚬ Type = id

    def act: Type -⚬ (Done |*| Type) =
      λ { as =>
        val names |*| as1 = unzipBy(fst(getName) > assocLR)(as) |> fst(toScalaList1)
        val +(done)       = names :>> printLine(formatMsg) :>> delayRandomMs(50, 100)
        val as2           = transform(useUntil)(done |*| as1)
        done |*| as2
      }

    def release: Type -⚬ One = foldMap(supply)

    private def useUntil: (Done |*| (A |*| -[A])) -⚬ (A |*| -[A]) =
      λ { case d |*| (a |*| nb) => a.waitFor(d) |*| nb }

    given Affine[Type] =
      Affine.from(foldMap(supply))

    given Signaling.Positive[Type] =
      Signaling.Positive.from(eachNotifyBy(fst(notifyPosFst[A]) > assocLR))
  }

  object RGroup extends Group[Reindeer](dup,names => s"Delivering toys with ${names.mkString(", ")}") {
    def deliverToys = act
  }

  object EGroup extends Group[Elf](dup, names => s"Meeting in study with ${names.mkString(", ")}") {
    def meetInStudy = act
  }

  import RGroup.{Type as RGroup, deliverToys}
  import EGroup.{Type as EGroup, meetInStudy}

  def santa(nCycles: Int): Endless[RGroup |+| EGroup] -⚬ Done = {
    def go: (RGroup |+| EGroup) -⚬ Done =
      either(
        deliverToys > elimSnd(RGroup.release),
        meetInStudy > elimSnd(EGroup.release),
      )

    mapSequentially(go) > take(nCycles) > LList.fold
  }

  override def blueprint: Done -⚬ Done =
    λ { case +(start) =>
      val reindeers : $[LList1[Reindeer]] = start :>> constList1Of("R1", "R2", "R3", "R4", "R5", "R6", "R7", "R8", "R9")
      val elves     : $[LList1[Elf]]      = start :>> constList1Of("E1", "E2", "E3", "E4", "E5", "E6", "E7", "E8", "E9", "E10")
      val reindeers1 = reindeers :>> map(vacation) :>> sortBySignal
      val elves1     = elves     :>> map(makeToys) :>> sortBySignal
      val rGroups |*| releasedReindeers = reindeers1 :>> Endless.poolReset(vacation) :>> fst(groupMap(9, RGroup.make))
      val eGroups |*| releasedElves     = elves1     :>> Endless.poolReset(makeToys) :>> fst(groupMap(3, EGroup.make))
      val groups: $[Endless[RGroup |+| EGroup]] = mergeEitherPreferred[RGroup, EGroup](rGroups |*| eGroups)
      joinAll(
        groups :>> santa(nCycles = 20),
        closeAll(releasedReindeers),
        closeAll(releasedElves),
      )
    }
}
