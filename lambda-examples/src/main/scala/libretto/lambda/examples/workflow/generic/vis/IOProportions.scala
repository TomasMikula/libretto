package libretto.lambda.examples.workflow.generic.vis

import scala.annotation.tailrec

import DefaultDimensions.Breadth
import IOLayout.EdgeLayout
import Px.px
import util.{IntegralProportions, leastCommonMultiple}

sealed trait IOProportions[I, O] {
  import IOProportions.*

  def totalBreadth: Breadth
  def inEdge: EdgeProportions[I]
  def outEdge: EdgeProportions[O]
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

    infix def combine[∙[_, _], Y](that: EdgeProportions[Y]): EdgeProportions[X ∙ Y] =
      EdgeProportions.Binary(this, that)

    def ∙[∙[_, _], Y](that: EdgeProportions[Y]): EdgeProportions[X ∙ Y] =
      this combine that
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
          if (whiteSpace % 2 == 0 || whiteSpace > 20)
            val pre  = whiteSpace / 2
            val post = whiteSpace - pre
            (scaleAcc, EdgeLayout.wire(pre.px, wireWidth, post.px))
          else
            place(scaleAcc * 2, scaledAvailableBreadth * 2, wireWidth * 2)

        go(1, availableBreadth)
      }
    }

    case class Binary[∙[_, _], X1, X2](x1: EdgeProportions[X1], x2: EdgeProportions[X2]) extends EdgeProportions[X1 ∙ X2] {
      override def totalBreadth: Breadth =
        Breadth.cram(x1.totalBreadth, x2.totalBreadth)

      override def layout(availableBreadth: Px): (Int, EdgeLayout[X1 ∙ X2]) = {
        Breadth.divideProportionally(availableBreadth.pixels)(x1.totalBreadth, x2.totalBreadth) match
          case IntegralProportions(i, List(w1, w2)) =>
            val (j1, layout1) = x1.layout(w1.px)
            val (j2, layout2) = x2.layout(w2.px)
            val (k1, k2, m) = leastCommonMultiple(j1, j2)
            (i * m, EdgeLayout.Par(layout1 * k1, layout2 * k2))
      }
    }

    case class Weighted[X](weight: Breadth, base: EdgeProportions[X]) extends EdgeProportions[X] {
      override def totalBreadth: Breadth = weight
      override def layout(availableBreadth: Px): (Int, EdgeLayout[X]) = base.layout(availableBreadth)
    }

    def unitSize: EdgeProportions[Wire] =
      UnitWire

    def default[X](x: EdgeDesc[X]): EdgeProportions[X] =
      x match
        case EdgeDesc.SingleWire =>
          UnitWire
        case p: EdgeDesc.Binary[op, x1, x2] =>
          Binary[op, x1, x2](default(p.x1), default(p.x2))
  }

  case class Separate[I, O](
    inEdge: EdgeProportions[I],
    outEdge: EdgeProportions[O],
  ) extends IOProportions[I, O] {
    override def totalBreadth: Breadth =
      Breadth.max(inEdge.totalBreadth, outEdge.totalBreadth)

    override def layout(availableBreadth: Px): (Int, IOLayout[I, O]) =
      val (ki, iLayout) = inEdge.layout(availableBreadth)
      val (ko, oLayout) = outEdge.layout(availableBreadth)
      val (li, lo, m) = leastCommonMultiple(ki, ko)
      (m, IOLayout.Separate(iLayout * li, oLayout * lo))

    override def layoutFw(iLayout: EdgeLayout[I]): (Int, IOLayout[I, O]) =
      val (ko, oLayout) = outEdge.layout(iLayout.pixelBreadth)
      (ko, IOLayout.Separate(iLayout * ko, oLayout))

    override def layoutBw(oLayout: EdgeLayout[O]): (Int, IOLayout[I, O]) =
      val (ki, iLayout) = inEdge.layout(oLayout.pixelBreadth)
      (ki, IOLayout.Separate(iLayout, oLayout * ki))
  }

  case class Par[∙[_, _], X1, X2, Y1, Y2](
    p1: IOProportions[X1, Y1],
    p2: IOProportions[X2, Y2],
  ) extends IOProportions[X1 ∙ X2, Y1 ∙ Y2] {
    override def totalBreadth: Breadth =
      Breadth.cram(p1.totalBreadth, p2.totalBreadth)

    override def inEdge: EdgeProportions[X1 ∙ X2] =
      EdgeProportions.Binary(p1.inEdge, p2.inEdge)

    override def outEdge: EdgeProportions[Y1 ∙ Y2] =
      EdgeProportions.Binary(p1.outEdge, p2.outEdge)

    override def layout(availableBreadth: Px): (Int, IOLayout[X1 ∙ X2, Y1 ∙ Y2]) = ???

    override def layoutFw(inLayout: EdgeLayout[X1 ∙ X2]): (Int, IOLayout[X1 ∙ X2, Y1 ∙ Y2]) =
      inLayout match
        case EdgeLayout.Par(l1, l2) =>
          val (i1, layout1) = p1.layoutFw(l1)
          val (i2, layout2) = p2.layoutFw(l2)
          val (j1, j2, m) = leastCommonMultiple(i1, i2)
          (m, IOLayout.Par(layout1 * j1, layout2 * j2))
        case EdgeLayout.SingleWire(pre, wire, post) =>
          throw AssertionError(s"Wire =:= (X1 ∙ X2) is impossible (unless ∙ is not a class type)")

    override def layoutBw(outLayout: EdgeLayout[Y1 ∙ Y2]): (Int, IOLayout[X1 ∙ X2, Y1 ∙ Y2]) =
      outLayout match
        case EdgeLayout.Par(l1, l2) =>
          val (i1, layout1) = p1.layoutBw(l1)
          val (i2, layout2) = p2.layoutBw(l2)
          val (j1, j2, m) = leastCommonMultiple(i1, i2)
          (m, IOLayout.Par(layout1 * j1, layout2 * j2))
        case EdgeLayout.SingleWire(pre, wire, post) =>
          throw AssertionError(s"Wire =:= (Y1 ∙ Y2) is impossible (unless ∙ is not a class type)")
  }

  case class Weighted[X, Y](
    weight: Breadth,
    base: IOProportions[X, Y],
  ) extends IOProportions[X, Y] {
    override def totalBreadth: Breadth = weight

    override def inEdge: EdgeProportions[X] =
      EdgeProportions.Weighted(weight, base.inEdge)

    override def outEdge: EdgeProportions[Y] =
      EdgeProportions.Weighted(weight, base.outEdge)

    override def layout(availableBreadth: Px): (Int, IOLayout[X, Y]) =
      base.layout(availableBreadth)

    override def layoutFw(inLayout: EdgeLayout[X]): (Int, IOLayout[X, Y]) =
      base.layoutFw(inLayout)

    override def layoutBw(outLayout: EdgeLayout[Y]): (Int, IOLayout[X, Y]) =
      base.layoutBw(outLayout)
  }
}
