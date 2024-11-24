package libretto.lambda.examples.workflow.generic.vis

import scala.annotation.tailrec
import scala.collection.immutable.{:: as NonEmptyList}

import DefaultDimensions.Breadth
import IOLayout.EdgeLayout
import Px.px
import util.{IntegralProportions, leastCommonMultiple}
import libretto.lambda.examples.workflow.generic.vis.IOLayout.EdgeLayout.TupleN

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

    case class TupleN[Wrap[_], X](
      components: TupleN.Components[Wrap, X],
    ) extends EdgeProportions[Wrap[X]] {
      override def totalBreadth: Breadth =
        val b0 :: bs = components.breadths
        Breadth.cram(b0, bs*)

      override def layout(availableBreadth: Px): (Int, EdgeLayout[Wrap[X]]) =
        Breadth.divideProportionally(availableBreadth.pixels)(
          components.breadths*
        ) match {
          case IntegralProportions(k, ws) =>
            val (l, compLayout) = components.layout(ws.map(Px(_)))
            (k * l, EdgeLayout.TupleN(compLayout))
        }
    }

    object TupleN {
      sealed trait Components[Wrap[_], X] {
        def breadths: NonEmptyList[Breadth] =
          breadths(Nil)

        private[TupleN] def breadths(tailAcc: List[Breadth]): NonEmptyList[Breadth]

        lazy val count =
          @tailrec def go[V](comps: Components[Wrap, V], acc: Int): Int =
            comps match
              case Single(_) => 1 + acc
              case Snoc(init, _) => go(init, 1 + acc)
          go(this, 0)

        def layout(ws: List[Px]): (Int, EdgeLayout.TupleN.Components[Wrap, X]) =
          assert(ws.size == count)
          layoutRev(ws.reverse)

        private[TupleN] def layoutRev(revBreadths: List[Px]): (Int, EdgeLayout.TupleN.Components[Wrap, X])
      }

      case class Single[Wrap[_], X](
        value: EdgeProportions[X],
      ) extends Components[Wrap, Only[X]] {
        override def breadths(tailAcc: List[Breadth]): NonEmptyList[Breadth] =
          NonEmptyList(value.totalBreadth, tailAcc)

        private[TupleN] override def layoutRev(revBreadths: List[Px]): (Int, EdgeLayout.TupleN.Components[Wrap, Only[X]]) =
          val w :: Nil = revBreadths
          val (k, layout) = value.layout(w)
          (k, EdgeLayout.TupleN.Single(layout))
      }

      case class Snoc[Wrap[_], X1, X2](
        init: Components[Wrap, X1],
        last: EdgeProportions[X2],
      ) extends Components[Wrap, (X1, X2)] {
        override def breadths(tailAcc: List[Breadth]): NonEmptyList[Breadth] =
          init.breadths(last.totalBreadth :: tailAcc)

        private[TupleN] override def layoutRev(revBreadths: List[Px]): (Int, EdgeLayout.TupleN.Components[Wrap, (X1, X2)]) =
          val wLast :: wInit = revBreadths
          val (k, lastLay) = last.layout(wLast)
          val (l, initLay) = init.layoutRev(wInit)
          (k * l, EdgeLayout.TupleN.Snoc(initLay, lastLay * l))
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
        case EdgeDesc.TupleN(_, components) =>
          TupleN(defaultTupleN(components))

    private def defaultTupleN[Wrap[_], X](
      x: EdgeDesc.TupleN.Components[Wrap, X],
    ): TupleN.Components[Wrap, X] =
      x match
        case EdgeDesc.TupleN.Single(d) => TupleN.Single(default(d))
        case EdgeDesc.TupleN.Snoc(init, last) => TupleN.Snoc(defaultTupleN(init), default(last))
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

    override def layout(availableBreadth: Px): (Int, IOLayout[X1 ∙ X2, Y1 ∙ Y2]) =
      Breadth.divideProportionally(availableBreadth.pixels)(
        p1.totalBreadth,
        p2.totalBreadth,
      ) match {
        case IntegralProportions(k, List(w1, w2)) =>
          val (k1, l1) = p1.layout(w1.px)
          val (k2, l2) = p2.layout(w2.px * k1)
          (k * k1 * k2, IOLayout.Par(l1 * k2, l2))
      }

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

  case class ParN[Wrap[_], X, Y](
    components: ParN.Components[Wrap, X, Y],
  ) extends IOProportions[Wrap[X], Wrap[Y]] {
    override def totalBreadth: Breadth =
      val b :: bs = components.breadths
      Breadth.cram(b, bs*)

    override def inEdge: EdgeProportions[Wrap[X]] =
      EdgeProportions.TupleN(components.inEdge)

    override def outEdge: EdgeProportions[Wrap[Y]] =
      EdgeProportions.TupleN(components.outEdge)

    override def layout(availableBreadth: Px): (Int, IOLayout[Wrap[X], Wrap[Y]]) =
      Breadth.divideProportionally(availableBreadth.pixels)(
        components.breadths*
      ) match {
        case IntegralProportions(k, ws) =>
          val (l, compLayout) = components.layout(ws.map(Px(_)))
          (k * l, IOLayout.ParN(compLayout))
      }

    override def layoutFw(inLayout: EdgeLayout[Wrap[X]]): (Int, IOLayout[Wrap[X], Wrap[Y]]) =
      inLayout match
        case EdgeLayout.TupleN(inLayoutComps) =>
          val (k, layoutComps) = components.layoutFw(inLayoutComps)
          (k, IOLayout.ParN(layoutComps))
        case _: EdgeLayout.Par[op, x1, x2] =>
          throw AssertionError(s"(x1 ∙ x2) =:= Wrap[X] is impossible if `∙` and `Wrap` are distinct class types")
        case _: EdgeLayout.SingleWire =>
          throw AssertionError(s"Wire =:= Wrap[X] is impossible (unless `Wrap` is not a class type)")

    override def layoutBw(outLayout: EdgeLayout[Wrap[Y]]): (Int, IOLayout[Wrap[X], Wrap[Y]]) =
      outLayout match
        case EdgeLayout.TupleN(outLayoutComps) =>
          val (k, layoutComps) = components.layoutBw(outLayoutComps)
          (k, IOLayout.ParN(layoutComps))
        case _: EdgeLayout.Par[op, y1, y2] =>
          throw AssertionError(s"(y1 ∙ y2) =:= Wrap[Y] is impossible if `∙` and `Wrap` are distinct class types")
        case _: EdgeLayout.SingleWire =>
          throw AssertionError(s"Wire =:= Wrap[Y] is impossible (unless `Wrap` is not a class type)")
  }

  object ParN {
    sealed trait Components[Wrap[_], X, Y] {
      def inEdge: EdgeProportions.TupleN.Components[Wrap, X]

      def outEdge: EdgeProportions.TupleN.Components[Wrap, Y]

      private[ParN] def layoutRev(revBreadths: List[Px]): (Int, IOLayout.ParN.Components[Wrap, X, Y])

      def layoutFw(inLayout: EdgeLayout.TupleN.Components[Wrap, X]): (Int, IOLayout.ParN.Components[Wrap, X, Y])

      def layoutBw(outLayout: EdgeLayout.TupleN.Components[Wrap, Y]): (Int, IOLayout.ParN.Components[Wrap, X, Y])

      def layout(breadths: List[Px]): (Int, IOLayout.ParN.Components[Wrap, X, Y]) =
        assert(breadths.size == count)
        layoutRev(breadths.reverse)

      lazy val count =
        @tailrec def go[V, W](comps: Components[Wrap, V, W], acc: Int): Int =
          comps match
            case Single(_) => 1 + acc
            case Snoc(init, _) => go(init, 1 + acc)
        go(this, 0)

      def breadths: NonEmptyList[Breadth] =
        breadths(Nil)

      private[ParN] def breadths(tail: List[Breadth]): NonEmptyList[Breadth]

      def nonEmptyIn(using X =:= EmptyTuple): Nothing
      def nonEmptyOut(using Y =:= EmptyTuple): Nothing
    }

    case class Single[Wrap[_], X, Y](
      value: IOProportions[X, Y],
    ) extends Components[Wrap, Only[X], Only[Y]] {
      override def nonEmptyIn(using Only[X] =:= EmptyTuple): Nothing =
        pairIsNotEmptyTuple[EmptyTuple, X]

      override def nonEmptyOut(using Only[Y] =:= EmptyTuple): Nothing =
        pairIsNotEmptyTuple[EmptyTuple, Y]

      override def breadths(tail: List[Breadth]): NonEmptyList[Breadth] =
        NonEmptyList(value.totalBreadth, tail)

      override def inEdge: EdgeProportions.TupleN.Components[Wrap, Only[X]] =
        EdgeProportions.TupleN.Single(value.inEdge)

      override def outEdge: EdgeProportions.TupleN.Components[Wrap, Only[Y]] =
        EdgeProportions.TupleN.Single(value.outEdge)

      private[ParN] override def layoutRev(
        revBreadths: List[Px],
      ): (Int, IOLayout.ParN.Components[Wrap, Only[X], Only[Y]]) =
        val w :: Nil = revBreadths
        val (k, layout) = value.layout(w)
        (k, IOLayout.ParN.Single(layout))

      override def layoutFw(
        inLayout: EdgeLayout.TupleN.Components[Wrap, Only[X]],
      ): (Int, IOLayout.ParN.Components[Wrap, Only[X], Only[Y]]) =
        inLayout match
          case EdgeLayout.TupleN.Single(inLayout) =>
            val (k, layout) = value.layoutFw(inLayout)
            (k, IOLayout.ParN.Single(layout))
          case EdgeLayout.TupleN.Snoc(initLay, _) =>
            initLay.nonEmpty

      override def layoutBw(
        outLayout: TupleN.Components[Wrap, Only[Y]],
      ): (Int, IOLayout.ParN.Components[Wrap, Only[X], Only[Y]]) =
        outLayout match
          case EdgeLayout.TupleN.Single(outLayout) =>
            val (k, layout) = value.layoutBw(outLayout)
            (k, IOLayout.ParN.Single(layout))
          case EdgeLayout.TupleN.Snoc(initLay, _) =>
            initLay.nonEmpty
    }

    case class Snoc[Wrap[_], X1, X2, Y1, Y2](
      init: Components[Wrap, X1, Y1],
      last: IOProportions[X2, Y2],
    ) extends Components[Wrap, (X1, X2), (Y1, Y2)] {
      override def nonEmptyIn(using (X1, X2) =:= EmptyTuple): Nothing =
        pairIsNotEmptyTuple[X1, X2]

      override def nonEmptyOut(using (Y1, Y2) =:= EmptyTuple): Nothing =
        pairIsNotEmptyTuple[Y1, Y2]

      override def breadths(tail: List[Breadth]): NonEmptyList[Breadth] =
        init.breadths(last.totalBreadth :: tail)

      override def inEdge: EdgeProportions.TupleN.Components[Wrap, (X1, X2)] =
        EdgeProportions.TupleN.Snoc(init.inEdge, last.inEdge)

      override def outEdge: EdgeProportions.TupleN.Components[Wrap, (Y1, Y2)] =
        EdgeProportions.TupleN.Snoc(init.outEdge, last.outEdge)

      override def layoutRev(revBreadths: List[Px]): (Int, IOLayout.ParN.Components[Wrap, (X1, X2), (Y1, Y2)]) =
        val lastW :: initWs = revBreadths
        val (k, lastLay) = last.layout(lastW)
        val (l, initLay) = init.layoutRev(initWs.map(_ * k))
        (k * l, IOLayout.ParN.Snoc(initLay, lastLay * l))

      override def layoutFw(
        inLayout: EdgeLayout.TupleN.Components[Wrap, (X1, X2)],
      ): (Int, IOLayout.ParN.Components[Wrap, (X1, X2), (Y1, Y2)]) =
        inLayout match
          case EdgeLayout.TupleN.Snoc(inLayInit, inLayLast) =>
            val (k, layInit) = init.layoutFw(inLayInit)
            val (l, layLast) = last.layoutFw(inLayLast * k)
            (k * l, IOLayout.ParN.Snoc(layInit * l, layLast))
          case EdgeLayout.TupleN.Single(value) =>
            init.nonEmptyIn(using summon[X1 =:= EmptyTuple])

      override def layoutBw(
        outLayout: EdgeLayout.TupleN.Components[Wrap, (Y1, Y2)],
      ): (Int, IOLayout.ParN.Components[Wrap, (X1, X2), (Y1, Y2)]) =
        outLayout match
          case EdgeLayout.TupleN.Snoc(outLayInit, outLayLast) =>
            val (k, layInit) = init.layoutBw(outLayInit)
            val (l, layLast) = last.layoutBw(outLayLast * k)
            (k * l, IOLayout.ParN.Snoc(layInit * l, layLast))
          case EdgeLayout.TupleN.Single(value) =>
            init.nonEmptyOut(using summon[Y1 =:= EmptyTuple])
    }
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
