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
    def pixelBreadth: Px
    def *(k: Int): EdgeLayout[X]

    def coordsOf(wire: WirePick[X]): EdgeLayout.WireCoords
    def coordsOf[W](seg: EdgeSegment[W, X]): EdgeLayout.SegmentCoords
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

      override def coordsOf(wire: WirePick[X1 ∙ X2]): WireCoords =
        wire.switch(
          caseId = (ev: (X1 ∙ X2) =:= Wire) ?=> ???,
          caseInl = [∘[_, _], A, B] => (ev: (X1 ∙ X2) =:= (A ∘ B)) ?=> (fst: WirePick[A]) => {
            l1
              .asInstanceOf[EdgeLayout[A]] // XXX: unsound without knowing that ∙ and ∘ are class types
              .coordsOf(fst)
          },
          caseInr = [∘[_, _], A, B] => (ev: (X1 ∙ X2) =:= (A ∘ B)) ?=> (snd: WirePick[B]) => {
            l2
              .asInstanceOf[EdgeLayout[B]] // XXX: unsound without knowing that ∙ and ∘ are class types
              .coordsOf(snd)
              .offset(l1.pixelBreadth)
          },
        )

      override def coordsOf[W](seg: EdgeSegment[W, X1 ∙ X2]): SegmentCoords =
        seg.switch(
          caseId = (ev: W =:= (X1 ∙ X2)) ?=> SegmentCoords(x = Px(0), pixelBreadth),
          caseInl = [∘[_, _], Y1, Q] => (ev: (X1 ∙ X2) =:= (Y1 ∘ Q)) ?=> (fst: EdgeSegment[W, Y1]) => {
            l1
              .asInstanceOf[EdgeLayout[Y1]] // XXX: unsound without knowing that ∙ and ∘ are class types
              .coordsOf(fst)
          },
          caseInr = [∘[_, _], Y2, P] => (ev: (X1 ∙ X2) =:= (P ∘ Y2)) ?=> (snd: EdgeSegment[W, Y2]) => {
            l2
              .asInstanceOf[EdgeLayout[Y2]] // XXX: unsound without knowing that ∙ and ∘ are class types
              .coordsOf(snd)
              .offset(l1.pixelBreadth)
          },
        )
    }

    case class SingleWire(pre: Px, wire: Px, post: Px) extends EdgeLayout[Wire] {
      override def pixelBreadth: Px = pre + wire + post
      override def *(k: Int): EdgeLayout[Wire] = SingleWire(pre * k, wire * k, post * k)

      override def coordsOf(pick: WirePick[Wire]): WireCoords =
        pick.switch(
          caseId = WireCoords(Px(0), pre, wire, post),
          caseInl = [∘[_, _], A, B] => (ev: Wire =:= (A ∘ B)) ?=> _ => Wire.isNotBinary[∘, A, B],
          caseInr = [∘[_, _], A, B] => (ev: Wire =:= (A ∘ B)) ?=> _ => Wire.isNotBinary[∘, A, B],
        )

      override def coordsOf[W](seg: EdgeSegment[W, Wire]): SegmentCoords =
        seg.switch(
          caseId = SegmentCoords(Px(0), pixelBreadth),
          caseInl = [∘[_, _], Y1, Q] => (ev: Wire =:= (Y1 ∘ Q)) ?=> (l: EdgeSegment[W, Y1]) => Wire.isNotBinary[∘, Y1, Q],
          caseInr = [∘[_, _], Y2, P] => (ev: Wire =:= (P ∘ Y2)) ?=> (l: EdgeSegment[W, Y2]) => Wire.isNotBinary[∘, P, Y2],
        )
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
