package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.TupleElem
import libretto.lambda.util.TypeEq
import libretto.lambda.util.TypeEq.Refl

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

    def coarsen[W](f: W IsRefinedBy X): EdgeLayout[W] =
      f match
        case IsRefinedBy.Id(desc) =>
          this
        case IsRefinedBy.Initial(outDesc) =>
          this.reallocateToSingleWire
        case p: IsRefinedBy.Pairwise[op, w1, w2, x1, x2] =>
          summon[W =:= (op[w1, w2])]
          this match
            case EdgeLayout.Par(l1, l2) =>
              EdgeLayout.Par[op, w1, w2](
                l1.coarsen(p.f1),
                l2.coarsen(p.f2)
              )
        case p: IsRefinedBy.ParN[wr, w, x] =>
          val IsRefinedBy.ParN(op, refinements) = p
          this match
            case EdgeLayout.TupleN(components) =>
              EdgeLayout.TupleN[wr, w](components.coarsen(refinements))

    protected def reallocateToSingleWire: EdgeLayout.SingleWire

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
          case EdgeSegment.InElem(_, _) =>
            throw AssertionError("Impossible if `Wrap` and `∙` are distinct class types")

      override def wireCoords(using ev: (X1 ∙ X2) =:= Wire): WireCoords =
        Wire.isNotBinary(using ev.flip)

      override def asSingleWire(using ev: (X1 ∙ X2) =:= Wire): SingleWire =
        Wire.isNotBinary(using ev.flip)

      override protected def reallocateToSingleWire: EdgeLayout.SingleWire =
        val SingleWire(pre1, w1, post1) = l1.reallocateToSingleWire
        val SingleWire(pre2, w2, post2) = l2.reallocateToSingleWire
        SingleWire(pre1 + post1, w1 + w2, pre2 + post2)
    }

    case class TupleN[Wrap[_], X](
      components: TupleN.Components[X],
    ) extends EdgeLayout[Wrap[X]] {
      override def pixelBreadth: Px =
        components.pixelBreadth

      override def *(k: Int): EdgeLayout[Wrap[X]] =
        TupleN(components * k)

      override def locate[W](seg: EdgeSegment[W, Wrap[X]]): (Px, EdgeLayout[W]) =
        seg match
          case EdgeSegment.Id() =>
            (Px(0), this)
          case EdgeSegment.InElem(nested, elem) =>
            val (off1, layout1) = components.locateElem(elem)
            val (off2, layout2) = layout1.locate(nested)
            (off1 + off2, layout2)
          case EdgeSegment.Inl(l) =>
            throw AssertionError("Impossible if `Wrap` and `∙` are distinct class types")
          case EdgeSegment.Inr(r) =>
            throw AssertionError("Impossible if `Wrap` and `∙` are distinct class types")


      override def wireCoords(using ev: Wrap[X] =:= Wire): WireCoords =
        throw AssertionError("Wrap[X] =:= Wire is impossible if Wrap is a class type distinct from Wire")

      override def asSingleWire(using Wrap[X] =:= Wire): SingleWire =
        throw AssertionError("Wrap[X] =:= Wire is impossible if Wrap is a class type distinct from Wire")

      override protected def reallocateToSingleWire: EdgeLayout.SingleWire =
        components.reallocateToSingleWire
    }

    object TupleN {
      import libretto.lambda.TupleN.{Single, Snoc}

      opaque type Components[X] = libretto.lambda.TupleN[Tuple2, EmptyTuple, EdgeLayout, X]

      extension [X] (thiz: Components[X]) {
        def pixelBreadth: Px =
          thiz match
            case Single(value)    => value.pixelBreadth
            case Snoc(init, last) => init.pixelBreadth + last.pixelBreadth

        def *(k: Int): Components[X] =
          thiz match
            case Single(value)    => Single(value * k)
            case Snoc(init, last) => Snoc(init * k, last * k)

        def locateElem[Xi](elem: TupleElem[Tuple2, EmptyTuple, Xi, X]): (Px, EdgeLayout[Xi]) =
          thiz match
            case Single(value)    => locateElemSingle(value, elem)
            case Snoc(init, last) => locateElemSnoc(init, last, elem)

        def coarsen[W](fs: IsRefinedBy.ParN.Components[W, X]): Components[W] =
          thiz match
            case Single(value)    => coarsenSingle(value, fs)
            case Snoc(init, last) => coarsenSnoc(init, last, fs)

        def reallocateToSingleWire: EdgeLayout.SingleWire =
          thiz match
            case Single(value) =>
              value.reallocateToSingleWire
            case Snoc(init, last) =>
              val SingleWire(pre1, w1, post1) = init.reallocateToSingleWire
              val SingleWire(pre2, w2, post2) = last.reallocateToSingleWire
              val w = w1 + w2
              val (pre, post) = (pre1 + post1 + pre2 + post2).halve
              SingleWire(pre, w, post)

      }

      def single[X](x: EdgeLayout[X]): Components[Only[X]] =
        Single(x)

      def snoc[X1, X2](init: Components[X1], last: EdgeLayout[X2]): Components[(X1, X2)] =
        Snoc(init, last)

      def extractSingle[X](xs: Components[Only[X]]): EdgeLayout[X] =
        xs match
          case Single(x) => x
          case s: Snoc[p, n, f, v, w] => s.init.nonEmpty([x11, x12] => ev ?=> pairIsNotEmptyTuple(using ev.flip))

      def unsnoc[X1, X2, X3](components: Components[((X1, X2), X3)]): (Components[(X1, X2)], EdgeLayout[X3]) =
        components match
          case Snoc(init, last) => (init, last)
          case Single(_) => throw AssertionError(s"Impossible `(X1, X2) =:= EmptyTuple`")

      private def coarsenSingle[X, W](
        x: EdgeLayout[X],
        fs: IsRefinedBy.ParN.Components[W, Only[X]],
      ): Components[W] =
        fs match
          case libretto.lambda.ParN.Single(f) =>
            Single(x.coarsen(f))
          case s: libretto.lambda.ParN.Snoc[p, n, f, w1, w2, x1, x2] =>
            s.init.nonEmptyOut([x, y] => pairIsNotEmptyTuple(using _))(summon[x1 =:= EmptyTuple])

      private def coarsenSnoc[X1, X2, W](
        init: Components[X1],
        last: EdgeLayout[X2],
        fs: IsRefinedBy.ParN.Components[W, (X1, X2)],
      ): Components[W] =
        fs match
          case libretto.lambda.ParN.Snoc(fInit, fLast) =>
            Snoc(init.coarsen(fInit), last.coarsen(fLast))
          case libretto.lambda.ParN.Single(_) =>
            init.nonEmpty { [x11, x12] => ev ?=> pairIsNotEmptyTuple(using ev.flip) }

      private def locateElemSingle[X, Xi](
        x: EdgeLayout[X],
        elem: TupleElem[Tuple2, EmptyTuple, Xi, (EmptyTuple, X)],
      ): (Px, EdgeLayout[Xi]) =
        elem match
          case TupleElem.Last() =>
            (Px(0), x)
          case TupleElem.InInit(init) =>
            init.ownerTypeAsTuple:
              [X, Y] => (ev: EmptyTuple =:= (X, Y)) ?=>
                throw AssertionError("Impossible: EmptyTuple =:= (X, Y)")

      private def locateElemSnoc[X1, X2, Xi](
        init: Components[X1],
        last: EdgeLayout[X2],
        elem: TupleElem[Tuple2, EmptyTuple, Xi, (X1, X2)],
      ): (Px, EdgeLayout[Xi]) =
        elem match
          case TupleElem.Last() =>
            (init.pixelBreadth, last)
          case TupleElem.InInit(elem1) =>
            init.locateElem(elem1)
    }

    case class SingleWire(pre: Px, wire: Px, post: Px) extends EdgeLayout[Wire] {
      override def pixelBreadth: Px = pre + wire + post
      override def *(k: Int): EdgeLayout[Wire] = SingleWire(pre * k, wire * k, post * k)

      override protected def reallocateToSingleWire: EdgeLayout.SingleWire = this

      override def locate[W](seg: EdgeSegment[W, Wire]): (Px, EdgeLayout[W]) =
        seg.switch(
          caseId = (ev: W =:= Wire) ?=> (Px(0), ev.substituteContra(this)),
          caseInl = [∘[_, _], Y1, Q] => (ev: Wire =:= (Y1 ∘ Q)) ?=> _ => Wire.isNotBinary[∘, Y1, Q],
          caseInr = [∘[_, _], Y2, P] => (ev: Wire =:= (P ∘ Y2)) ?=> _ => Wire.isNotBinary[∘, P, Y2],
          caseElem = [Wrap[_], T, Ts] => (ev: Wire =:= Wrap[Ts]) ?=> (_, _) =>
            throw AssertionError(s"Wire =:= Wrap[Ts] is impossible if Wrap is a class type distinct from Wire"),
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
          case SubWire.PaddingMidpoints => SegmentCoords(pre.lHalf, pre.rHalf + wire + post.lHalf)
          case SubWire.Fraction(i, j, n) =>
            val a = wire * i / n
            val b = wire * j / n
            SegmentCoords(pre + a, Px(b.pixels - a.pixels))
      }

      private[EdgeLayout] def locatePoint(p: EdgeStretch.InnerPointOf.SubWirePoint): Px = {
        import EdgeStretch.InnerPointOf.SubWirePoint.*

        p match
          case WireBegin => pre
          case WireMid   => pre + wire.lHalf
          case WireEnd   => pre + wire
          case LPadMid   => pre.lHalf
          case RPadMid   => pre + wire + post.lHalf
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

    def asTupleN[Wrap[_], X](x: EdgeLayout[Wrap[X]]): TupleN[Wrap, X] =
      x match
        case t @ TupleN(_) => t

    def single[Wrap[_], X](x: EdgeLayout[Wrap[(EmptyTuple, X)]]): EdgeLayout[X] =
      x match
        case TupleN(components) =>
          TupleN.extractSingle(components)

    def unsnoc[Wrap[_], X1, X2, X3](
      x: EdgeLayout[Wrap[((X1, X2), X3)]],
    ): (EdgeLayout[Wrap[(X1, X2)]], EdgeLayout[X3]) =
      x match
        case TupleN(components) =>
          val (init, last) = TupleN.unsnoc(components)
          (TupleN(init), last)
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

  case class ParN[Wrap[_], I, O](
    components: ParN.Components[I, O],
  ) extends IOLayout[Wrap[I], Wrap[O]] {
    override def pixelBreadth: Px =
      components.pixelBreadth

    override def inEdge: EdgeLayout[Wrap[I]] =
      EdgeLayout.TupleN(components.inEdge)

    override def outEdge: EdgeLayout[Wrap[O]] =
      EdgeLayout.TupleN(components.outEdge)

    override def *(k: Int): IOLayout[Wrap[I], Wrap[O]] =
      ParN(components * k)
  }

  object ParN {
    import libretto.lambda.ParN.{Single, Snoc}

    opaque type Components[I, O] = libretto.lambda.ParN[Tuple2, EmptyTuple, IOLayout, I, O]

    extension [I, O] (thiz: Components[I, O]) {
      def pixelBreadth: Px =
        thiz match
          case Single(value) => value.pixelBreadth
          case Snoc(init, last) => init.pixelBreadth + last.pixelBreadth

      def inEdge: EdgeLayout.TupleN.Components[I] =
        thiz match
          case Single(value)    => EdgeLayout.TupleN.single(value.inEdge)
          case Snoc(init, last) => EdgeLayout.TupleN.snoc(init.inEdge, last.inEdge)

      def outEdge: EdgeLayout.TupleN.Components[O] =
        thiz match
          case Single(value)    => EdgeLayout.TupleN.single(value.outEdge)
          case Snoc(init, last) => EdgeLayout.TupleN.snoc(init.outEdge, last.outEdge)

      def *(k: Int): Components[I, O] =
        thiz match
          case Single(value)    => Single(value * k)
          case Snoc(init, last) => Snoc(init * k, last * k)
    }

    def single[I, O](value: IOLayout[I, O]): Components[Only[I], Only[O]] =
      Single(value)

    def snoc[I1, I2, O1, O2](
      init: Components[I1, O1],
      last: IOLayout[I2, O2],
    ): Components[(I1, I2), (O1, O2)] =
      Snoc(init, last)

    def extractSingle[X, Y](comps: Components[Only[X], Only[Y]]): IOLayout[X, Y] =
      comps match
        case Single(c) => c
        case s: Snoc[p, n, f, v1, v2, w1, w2] => s.init.nonEmpty([x11, x12, y11, y12] => (evx, evy) ?=> pairIsNotEmptyTuple(using evx.flip))

    def unsnoc[X1, X2, X3, Y1, Y2, Y3](
      comps: Components[((X1, X2), X3), ((Y1, Y2), Y3)]
    ): (Components[(X1, X2), (Y1, Y2)], IOLayout[X3, Y3]) =
      comps match
        case Snoc(init, last) => (init, last)
        case Single(_) => throw AssertionError(s"Impossible `(X1, X2) =:= EmptyTuple`")
  }
}
