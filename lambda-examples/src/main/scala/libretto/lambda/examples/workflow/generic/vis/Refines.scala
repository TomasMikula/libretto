package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.{Some as ∃}

infix sealed trait Refines[X, Y] {
  def pair[V, W](that: V Refines W): (X, V) Refines (Y, W) =
    Refines.Pair(this, that)

  /** Returns the most refined `W` such that `W` is a coarsening of both `Y` and `Z`. */
  infix def greatestCommonCoarsening[Z](
    that: X Refines Z,
  ): Exists[[W] =>>(
    Y Refines W,
    Z Refines W,
  )]

  /** Two (potentially different) coarsenings of `X` can be morphed into each other. */
  infix def morph[Z](that: X Refines Z): Morph[Y, Z]

  def toMorph: Morph[X, Y] =
    Morph.Contra(this)
}

object Refines {
  case class Id[X]() extends Refines[X, X] {
    override def greatestCommonCoarsening[Z](
      that: X Refines Z,
    ): Exists[[W] =>> (X Refines W, Z Refines W)] =
      Exists((that, Id[Z]()))

    override def morph[Z](that: X Refines Z): Morph[X, Z] =
      Morph.Contra(that)
  }

  case class Terminal[X]() extends Refines[X, Wire] {
    override def greatestCommonCoarsening[Z](
      that: X Refines Z,
    ): Exists[[W] =>> (Wire Refines W, Z Refines W)] =
      Exists((Id[Wire](), Terminal[Z]()))

    override def morph[Z](that: X Refines Z): Morph[Wire, Z] =
      Morph.Co(Terminal[Z]())
  }

  case class Pair[X1, X2, Y1, Y2](
    f1: X1 Refines Y1,
    f2: X2 Refines Y2,
  ) extends Refines[(X1, X2), (Y1, Y2)] {
    override def greatestCommonCoarsening[Z](
      that: (X1, X2) Refines Z,
    ): Exists[[W] =>> ((Y1, Y2) Refines W, Z Refines W)] =
      that match
        case Id() => Exists((Id(), this))
        case Terminal() => Exists((Terminal(), Id()))
        case Pair(g1, g2) => greatestCommonCoarseningPair(g1, g2)

    private def greatestCommonCoarseningPair[Z1, Z2](
      g1: X1 Refines Z1,
      g2: X2 Refines Z2,
    ): Exists[[W] =>> ((Y1, Y2) Refines W, (Z1, Z2) Refines W)] =
      (f1 greatestCommonCoarsening g1, f2 greatestCommonCoarsening g2) match
        case (∃((wf1, wg1)), ∃((wf2, wg2))) =>
          Exists((Pair(wf1, wf2), Pair(wg1, wg2)))

    override def morph[Z](
      that: (X1, X2) Refines Z,
    ): Morph[(Y1, Y2), Z] =
      that match
        case Id() => Morph.Co(this)
        case Terminal() => Morph.Contra(Terminal())
        case Pair(g1, g2) => morphToPair(g1, g2)

    private def morphToPair[Z1, Z2](
      g1: X1 Refines Z1,
      g2: X2 Refines Z2,
    ): Morph[(Y1, Y2), (Z1, Z2)] =
      Morph.par(f1 morph g1, f2 morph g2)
  }

  def id[X]: Refines[X, X] =
    Id()

  def anythingRefinesWire[X]: Refines[X, Wire] =
    Terminal()
}
