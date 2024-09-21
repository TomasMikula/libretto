package libretto.lambda.examples.workflow.generic.vis

import scala.annotation.tailrec

import DefaultDimensions.Breadth
import IOLayout.EdgeLayout
import Px.px
import util.leastCommonMultiple
import libretto.lambda.examples.workflow.generic.vis.util.IntegralProportions

sealed trait IOProportions[I, O] {
  def totalBreadth: Breadth
  def layout(availableBreadth: Px): (Int, IOLayout[I, O])
  def layoutFw(inLayout: EdgeLayout[I]): (Int, IOLayout[I, O])
  def layoutBw(outLayout: EdgeLayout[O]): (Int, IOLayout[I, O])
}

object IOProportions {
  /** The minimum fraction of available breadth to be taken by the wire. */
  private val WireFractionMin = 0.13

  /** The preferred fraction of available breadth to be taken by the wire. */
  private val WireFraction = 0.15

  /** The maximum fraction of available breadth to be taken by the wire. */
  private val WireFractionMax = 0.17

  sealed trait EdgeProportions[X] {
    def totalBreadth: Breadth
    def layout(availableBreadth: Px): (Int, EdgeLayout[X])

    infix def pair[Y](that: EdgeProportions[Y]): EdgeProportions[(X, Y)] =
      EdgeProportions.Pair(this, that)
  }

  object EdgeProportions {
    case object UnitWire extends EdgeProportions[Wire] {
      override def totalBreadth: Breadth = Breadth.one

      override def layout(availableBreadth: Px): (Int, EdgeLayout[Wire]) = {
        require(availableBreadth.pixels > 0)

        @tailrec
        def go(scaleAcc: Int, scaledAvailableBreadth: Px): (Int, EdgeLayout[Wire]) =
          val lo = WireFractionMin * scaledAvailableBreadth.pixels
          val hi = WireFractionMax * scaledAvailableBreadth.pixels
          val w = math.round(WireFraction * scaledAvailableBreadth.pixels).toInt
          if (lo <= w && w <= hi)
            place(scaleAcc, scaledAvailableBreadth, Px(w))
          else
            go(scaleAcc + 1, scaledAvailableBreadth + availableBreadth)

        def place(scaleAcc: Int, scaledAvailableBreadth: Px, wireWidth: Px): (Int, EdgeLayout[Wire]) =
          val whiteSpace = scaledAvailableBreadth.pixels - wireWidth.pixels
          if (whiteSpace % 2 == 0)
            val pad = whiteSpace / 2
            (scaleAcc, EdgeLayout.wire(pad.px, wireWidth, pad.px))
          else
            place(scaleAcc * 2, scaledAvailableBreadth * 2, wireWidth * 2)

        go(1, availableBreadth)
      }
    }

    case class Pair[X1, X2](x1: EdgeProportions[X1], x2: EdgeProportions[X2]) extends EdgeProportions[(X1, X2)] {
      override def totalBreadth: Breadth =
        Breadth.cram(x1.totalBreadth, x2.totalBreadth)

      override def layout(availableBreadth: Px): (Int, EdgeLayout[(X1, X2)]) = {
        Breadth.divideProportionally(availableBreadth.pixels)(x1.totalBreadth, x2.totalBreadth) match
          case IntegralProportions(i, List(w1, w2)) =>
            val (j1, layout1) = x1.layout(w1.px)
            val (j2, layout2) = x2.layout(w2.px)
            val (k1, k2, m) = leastCommonMultiple(j1, j2)
            (i * m, EdgeLayout.pair(layout1 * k1, layout2 * k2))
      }
    }

    def unitWire: EdgeProportions[Wire] =
      UnitWire
  }

  case class Unimplemented[I, O](totalBreadth: Breadth) extends IOProportions[I, O] {
    override def layout(availableBreadth: Px): (Int, IOLayout[I, O]) =
      (1, IOLayout.Unimplemented(availableBreadth))

    override def layoutFw(inLayout: EdgeLayout[I]): (Int, IOLayout[I, O]) =
      (1, IOLayout.Unimplemented(inLayout.pixelBreadth))

    override def layoutBw(outLayout: EdgeLayout[O]): (Int, IOLayout[I, O]) =
      (1, IOLayout.Unimplemented(outLayout.pixelBreadth))
  }

  case class Separate[I, O](
    in: EdgeProportions[I],
    out: EdgeProportions[O],
  ) extends IOProportions[I, O] {
    override def totalBreadth: Breadth =
      Breadth.max(in.totalBreadth, out.totalBreadth)

    override def layout(availableBreadth: Px): (Int, IOLayout[I, O]) =
      val (ki, iLayout) = in.layout(availableBreadth)
      val (ko, oLayout) = out.layout(availableBreadth)
      val (li, lo, m) = leastCommonMultiple(ki, ko)
      (m, IOLayout.Separate(iLayout * li, oLayout * lo))

    override def layoutFw(iLayout: EdgeLayout[I]): (Int, IOLayout[I, O]) =
      val (ko, oLayout) = out.layout(iLayout.pixelBreadth)
      (ko, IOLayout.Separate(iLayout * ko, oLayout))

    override def layoutBw(oLayout: EdgeLayout[O]): (Int, IOLayout[I, O]) =
      val (ki, iLayout) = in.layout(oLayout.pixelBreadth)
      (ki, IOLayout.Separate(iLayout, oLayout * ki))
  }
}
