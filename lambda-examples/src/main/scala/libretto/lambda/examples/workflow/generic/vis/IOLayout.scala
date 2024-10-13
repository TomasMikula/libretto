package libretto.lambda.examples.workflow.generic.vis

sealed trait IOLayout[I, O] {
  import IOLayout.*

  def pixelBreadth: Px
  def inEdge: EdgeLayout[I]
  def outEdge: EdgeLayout[O]
  def *(k: Int): IOLayout[I, O]

  def separate: (EdgeLayout[I], EdgeLayout[O]) =
    (inEdge, outEdge)
}

object IOLayout {
  sealed trait EdgeLayout[X] {
    import EdgeLayout.*

    def pixelBreadth: Px
    def *(k: Int): EdgeLayout[X]

    def locate[W](seg: EdgeSegment[W, X]): (Px, EdgeLayout[W])
    def wireCoords(using ev: X =:= Wire): WireCoords
    def asSingleWire(using X =:= Wire): EdgeLayout.SingleWire

    def wireCoords(wire: WirePick[X]): EdgeLayout.WireCoords =
      val seg: EdgeSegment[Wire, X] = wire
      val (x, w) = locate(seg)
      w.wireCoords.offset(x)

    def coordsOf(str: EdgeStretch[X]): SegmentCoords =
      str match
        case EdgeStretch.SinglePoint(p) =>
          SegmentCoords(locatePoint(p), Px(0))
        case EdgeStretch.Line(leastCover, demarcation) =>
          val (offset, w) = locate(leastCover)
          w.coordsOf(demarcation).offset(offset)

    private def coordsOf(dem: EdgeStretch.Demarcation[X]): SegmentCoords =
      import EdgeStretch.{Demarcation => Dem}
      dem match
        case Dem.Whole() =>
          SegmentCoords(Px(0), this.pixelBreadth)
        case ld: Dem.Leading[op, x1, x2] =>
          val (l1, l2) = EdgeLayout.split[op, x1, x2](this)
          SegmentCoords(Px(0), l1.pixelBreadth + l2.locatePoint(ld.to))
        case tr: Dem.Trailing[op, x1, x2] =>
          val (l1, l2) = EdgeLayout.split[op, x1, x2](this)
          val x = l1.locatePoint(tr.from)
          val w = Px(this.pixelBreadth.pixels - x.pixels)
          SegmentCoords(x, w)
        case inn: Dem.Inner[op, x1, x2] =>
          val (l1, l2) = EdgeLayout.split[op, x1, x2](this)
          val x1 = l1.locatePoint(inn.from)
          val x2 = l2.locatePoint(inn.to) + l1.pixelBreadth
          val w = Px(x2.pixels - x1.pixels)
          SegmentCoords(x1, w)
        case sub: Dem.SubWire =>
          this.asSingleWire.subwireCoords(sub)

    def locatePoint(p: EdgeStretch.PointOf[X]): Px = {
      import EdgeStretch.InnerPointOf
      p match
        case EdgeStretch.StartOf() => Px(0)
        case EdgeStretch.EndOf() => pixelBreadth
        case bw: EdgeStretch.InnerPointOf.Between[op, x1, x2, y] =>
          val (offset, layout) = locate(bw.seg)
          val (l1, _) = EdgeLayout.split[op, x1, x2](layout)
          offset + l1.pixelBreadth
        case EdgeStretch.InnerPointOf.SubWire(seg, p) =>
          val (offset, layout) = locate(seg)
          offset + layout.asSingleWire.locatePoint(p)
    }
  }

  object EdgeLayout {
    case class Par[∙[_, _], X1, X2](
      l1: EdgeLayout[X1],
      l2: EdgeLayout[X2],
    ) extends EdgeLayout[X1 ∙ X2] {
      override def pixelBreadth: Px =
        l1.pixelBreadth + l2.pixelBreadth

      override def *(k: Int): EdgeLayout[X1 ∙ X2] =
        Par(l1 * k, l2 * k)

      override def locate[W](seg: EdgeSegment[W, X1 ∙ X2]): (Px, EdgeLayout[W]) =
        seg match
          case EdgeSegment.Id()   => (Px(0), this)
          case EdgeSegment.Inl(l) => l1.locate(l)
          case EdgeSegment.Inr(r) => l2.locate(r) match { case (x, w) => (l1.pixelBreadth + x, w) }

      override def wireCoords(using ev: (X1 ∙ X2) =:= Wire): WireCoords =
        Wire.isNotBinary(using ev.flip)

      override def asSingleWire(using ev: (X1 ∙ X2) =:= Wire): SingleWire =
        Wire.isNotBinary(using ev.flip)
    }

    case class SingleWire(pre: Px, wire: Px, post: Px) extends EdgeLayout[Wire] {
      override def pixelBreadth: Px = pre + wire + post
      override def *(k: Int): EdgeLayout[Wire] = SingleWire(pre * k, wire * k, post * k)

      override def locate[W](seg: EdgeSegment[W, Wire]): (Px, EdgeLayout[W]) =
        seg.switch(
          caseId = (ev: W =:= Wire) ?=> (Px(0), ev.substituteContra(this)),
          caseInl = [∘[_, _], Y1, Q] => (ev: Wire =:= (Y1 ∘ Q)) ?=> _ => Wire.isNotBinary[∘, Y1, Q],
          caseInr = [∘[_, _], Y2, P] => (ev: Wire =:= (P ∘ Y2)) ?=> _ => Wire.isNotBinary[∘, P, Y2],
        )

      override def wireCoords(using ev: Wire =:= Wire): WireCoords =
        WireCoords(Px(0), pre, wire, post)

      override def asSingleWire(using Wire =:= Wire): SingleWire =
        this

      private[EdgeLayout] def subwireCoords(
        sub: EdgeStretch.Demarcation.SubWire,
      ): SegmentCoords = {
        import EdgeStretch.Demarcation.SubWire

        sub match
          case SubWire.Pre         => SegmentCoords(Px(0), pre)
          case SubWire.WireLHalf   => SegmentCoords(pre, wire.lHalf)
          case SubWire.WireRHalf   => SegmentCoords(pre + wire.lHalf, wire.rHalf)
          case SubWire.Post        => SegmentCoords(pre + wire, post)
          case SubWire.LHalf       => SegmentCoords(Px(0), pre + wire.lHalf)
          case SubWire.RHalf       => SegmentCoords(pre + wire.lHalf, wire.rHalf + post)
          case SubWire.WireOnly    => SegmentCoords(pre, wire)
          case SubWire.WireAndPre  => SegmentCoords(Px(0), pre + wire)
          case SubWire.WireAndPost => SegmentCoords(pre, wire + post)
      }

      private[EdgeLayout] def locatePoint(p: EdgeStretch.InnerPointOf.SubWirePoint): Px = {
        import EdgeStretch.InnerPointOf.SubWirePoint.*

        p match
          case WireBegin => pre
          case WireMid   => pre + wire.lHalf
          case WireEnd   => pre + wire
      }

      extension (w: Px)
        private def lHalf: Px = w/2
        private def rHalf: Px = Px(w.pixels - w.pixels/2)
    }

    case class WireCoords(segmentX: Px, pre: Px, wireWidth: Px, post: Px) {
      def wireX: Px = segmentX + pre
      def segmentWidth: Px = pre + wireWidth + post

      def offset(x: Px): WireCoords =
        copy(segmentX = x + segmentX)
    }

    case class SegmentCoords(x: Px, width: Px) {
      def offset(xOffset: Px): SegmentCoords =
        copy(x = xOffset + x)
    }

    def wire(pre: Px, wire: Px, post: Px): EdgeLayout[Wire] =
      SingleWire(pre, wire, post)

    def pair[X, Y](x: EdgeLayout[X], y: EdgeLayout[Y]): EdgeLayout[(X, Y)] =
      Par(x, y)

    // TODO: for soundness, require evidence that ∙ is a class type
    def split[∙[_, _], X1, X2](x: EdgeLayout[X1 ∙ X2]): (EdgeLayout[X1], EdgeLayout[X2]) =
      x match
        case Par(l1, l2) => (l1, l2)
        case SingleWire(pre, wire, post) =>
          throw AssertionError(s"Impossible Wire =:= (X1 ∙ X2). Unless ∙ is not a class type.")
  }

  case class Separate[I, O](
    inEdge: EdgeLayout[I],
    outEdge: EdgeLayout[O],
  ) extends IOLayout[I, O] {
    override def pixelBreadth: Px =
      Px.max(inEdge.pixelBreadth, outEdge.pixelBreadth)

    override def *(k: Int): IOLayout[I, O] =
      Separate(inEdge * k, outEdge * k)
  }

  case class Par[∙[_, _], I1, I2, O1, O2](
    l1: IOLayout[I1, O1],
    l2: IOLayout[I2, O2],
  ) extends IOLayout[I1 ∙ I2, O1 ∙ O2] {
    override def pixelBreadth: Px =
      l1.pixelBreadth + l2.pixelBreadth

    override def inEdge: EdgeLayout[I1 ∙ I2] =
      EdgeLayout.Par(l1.inEdge, l2.inEdge)

    override def outEdge: EdgeLayout[O1 ∙ O2] =
      EdgeLayout.Par(l1.outEdge, l2.outEdge)

    override def *(k: Int): IOLayout[I1 ∙ I2, O1 ∙ O2] =
      require(k > 0)
      Par(l1 * k, l2 * k)
  }
}
