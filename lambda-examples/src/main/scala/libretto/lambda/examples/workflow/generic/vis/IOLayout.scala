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

    def segmentCoords[W](seg: EdgeSegment[W, X] | EdgeSegment.SubWire[X]): SegmentCoords =
      seg match
        case seg: EdgeSegment[W, X] =>
          val (x, wl) = locate(seg)
          SegmentCoords(x, wl.pixelBreadth)
        case seg: EdgeSegment.SubWire[X] =>
          seg match
            case EdgeSegment.SubWire.WireOnly(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x + pre, w)
            case EdgeSegment.SubWire.Pre(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x, pre)
            case EdgeSegment.SubWire.Post(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x + pre + w, post)
            case EdgeSegment.SubWire.WireAndPre(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x, pre + w)
            case EdgeSegment.SubWire.WireAndPost(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x + pre, w + post)
            case EdgeSegment.SubWire.MidPoint(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x + pre + w/2, Px(0))
            case EdgeSegment.SubWire.WireLHalf(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) => SegmentCoords(x + pre, w/2)
            case EdgeSegment.SubWire.WireRHalf(seg) =>
              wireCoords(seg) match
                case WireCoords(x, pre, w, post) =>
                  val w2 = Px(w.pixels - w.pixels/2)
                  SegmentCoords(x + pre + w/2, w2)

    def wireCoords(wire: WirePick[X]): EdgeLayout.WireCoords =
      val seg: EdgeSegment[Wire, X] = wire
      val (x, w) = locate(seg)
      w.wireCoords.offset(x)
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
