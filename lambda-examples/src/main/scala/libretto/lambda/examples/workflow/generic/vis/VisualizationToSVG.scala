package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.Color
import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.examples.workflow.generic.vis.Px.*
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily.{Monospace, Serif}
import libretto.lambda.examples.workflow.generic.vis.SVG.{Stroke, TextAnchor}
import libretto.lambda.examples.workflow.generic.vis.util.{IntegralProportions, leastCommonMultiple}
import scala.math.Ordering.Implicits.*

import IOLayout.EdgeLayout
import IOProportions.EdgeProportions

object VisualizationToSVG {
  def renderSVGToFit(g: Visualization[?, ?], W: Int, H: Int): SVGDocument =
    val edges = g.ioProportions
    val r = AspectRatio(g.length, edges.totalBreadth)
    val (w, h) = r.scaleToFit(W, H)
    val (k, layout) = edges.layout(w.px)

    SVGDocument(
      renderSVG(g, layout, Px(h) * k)
    )

  def renderSVG[X, Y](g: Visualization[X, Y], edges: IOLayout[X, Y], height: Px): SVGElem =
    println(s"rendering ${g.getClass.getSimpleName} into ${edges.pixelBreadth} x $height")
    g match
      case seq: Visualization.Sequence[x, y] =>
        renderSequence(seq, edges, height)
      case par: Visualization.Par[bin, x1, x2, y1, y2] =>
        renderPar(par, edges, height)
      case Visualization.ConnectorsOverlay(base, connectors) =>
        val conns = renderConnectors(connectors, edges, height)
        base match
          case Left(vis) =>
            val back = renderSVG(vis, edges, height)
            SVGElem.Group(back, conns)
          case Right(props) =>
            conns
      case Visualization.Text(value, props, vpos) =>
        renderText(value, edges.pixelBreadth, height, 0.6, vpos, Serif)
      case Visualization.LabeledBox(i, o, label, fillOpt) =>
        val width = edges.pixelBreadth
        val strokeWidth = math.min(width.pixels / 20.0, height.pixels / 20.0)
        val r = 0.15 * math.min(width.pixels, height.pixels)
        val rect = SVGElem.Rect(0.px, 0.px, width, height, fillOpt, Some(Stroke(strokeWidth, Color.Black)), clipPath = None, rx = Some(r), ry = Some(r))
        val txt = renderText(label, width, height, 0.6, VPos.Middle, Monospace)
        SVGElem.Group(rect, txt)
      case Visualization.WithBackgroundBox(fillOpt, strokeOpt, front) =>
        val width = edges.pixelBreadth
        val strokeWidth = math.min(width.pixels / 20.0, height.pixels / 20.0)
        val back = SVGElem.Rect(0.px, 0.px, width, height, fillOpt, strokeOpt.map(Stroke(strokeWidth, _)), clipPath = Some(SVG.ClipPath.FillBox))
        SVGElem.Group(back, renderSVG(front, edges, height))
      case Visualization.Adapt(f) =>
        val (i, o) = edges.separate
        renderAdapt(f, TrapezoidLayout(i, o, height))
      case Visualization.Unimplemented(label, _, _) =>
        renderUnimplemented(label, edges.pixelBreadth, height)

  private def renderUnimplemented[X, Y](label: String, width: Px, height: Px): SVGElem =
    val text = SVGElem.Text(label, x = 0.px, y = 20.px, Monospace, fontSize = 20.px)
    val textH = text.fontSize.pixels
    val textW = (label.length * textH * 3 + 4) / 5 // XXX: just a guess that character width is 3/5 of font size
    val scale =
      height.pixels match
        case 0      => 0.0
        case height => scaleToFit(textW, textH, width.pixels, height).toDouble
    SVGElem.Group(
      SVGElem.Rect.outlineInner(width, height, math.min(width.pixels / 20.0, height.pixels / 20.0), Color.Red),
      text.scale(scale)
    )

  /** Render horizontally centered text, at the bottom of the given width x height rectangle.
   *
   * @param textHeightProportion maximum proportion of vertical space to be taken by the text. Must be from (0.0, 1.0].
   */
  private def renderText(value: String, width: Px, height: Px, textHeightProportion: Double, vpos: VPos, fontFamily: FontFamily): SVGElem = {
    require(width.pixels > 0)
    require(height.pixels > 0)
    require(textHeightProportion >  0.0)
    require(textHeightProportion <= 1.0)

    if (textHeightProportion == 1.0)
      renderText(value, width, height, height, vpos, fontFamily)
    else
      IntegralProportions.divideProportionally(height.pixels)(Array(
        textHeightProportion,
        1.0 - textHeightProportion,
      )) match
        case IntegralProportions(k, List(textH, vPad)) =>
          val g = renderText(value, width * k, height * k, textH.px, vpos, fontFamily)
          if k == 1 then g else g.scale(1.0 / k)
  }

  private def renderText(value: String, width: Px, height: Px, textHeight: Px, vpos: VPos, fontFamily: FontFamily): SVGElem = {
    require(0 < textHeight.pixels)
    require(    textHeight.pixels <= height.pixels)

    val maxTextHeight = (width.pixels * 5 - 4) / (3 * value.length) // XXX: just a guess that character width is 3/5 of font size
    val fontSize = Px.min(textHeight, maxTextHeight.px)
    val y = vpos match
      case VPos.Bottom => height
      case VPos.Top => fontSize
      case VPos.Middle => (height + fontSize) / 2
    SVGElem.Text(value, x = width / 2, y = y, fontFamily, fontSize, TextAnchor.Middle)
  }

  private def renderSequence[X, Y](
    seq: Visualization.Sequence[X, Y],
    edges: IOLayout[X, Y],
    height: Px,
  ): SVGElem = {
    Length.divideProportionally(height.pixels)(seq.lengths*) match
      case IntegralProportions(k, heights) =>
        assert(heights.size == seq.size)
        val (l, vs) = renderSequence(seq, edges.inEdge * k, edges.outEdge * k, heights.map(Px(_)), yOffset = 0.px)
        val g = SVGElem.Group(vs)
        val kl = k * l
        if (kl == 1) then g else g.scale(1.0 / kl)
  }

  private def renderSequence[X, Y](
    seq: Visualization.Sequence[X, Y],
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    heights: List[Px],
    yOffset: Px,
  ): (Int, List[SVGElem]) = {
    require(heights.size == seq.size)

    seq match
      case Visualization.Sequence.Two(fst, flexiSnd) =>
        ???
        val (k, fstLayout) = fst.ioProportions.layoutFw(iLayout)
        val h1 = heights.head * k
        val yk = yOffset * k
        val fstVis = renderSVG(fst, fstLayout, h1).optTranslateY(yk.pixels)
        val sndVis = renderSVG(flexiSnd, IOLayout.Separate(fstLayout.outEdge, oLayout * k), heights(1) * k).translateY((yk + h1).pixels)
        (k, List(fstVis, sndVis))
      case Visualization.Sequence.TwoFlexiFst(flexiFst, snd) =>
        val (k, sndLayout) = snd.ioProportions.layoutBw(oLayout)
        val yk = yOffset * k
        val h1 = heights.head * k
        val sndVis = renderSVG(snd, sndLayout, heights(1) * k).translateY((yk + h1).pixels)
        val fstVis = renderSVG(flexiFst, IOLayout.Separate(iLayout * k, sndLayout.inEdge), h1).optTranslateY(yk.pixels)
        (k, List(fstVis, sndVis))
      case Visualization.Sequence.Cons(head, tail) =>
        val (k, headLayout) = head.ioProportions.layoutFw(iLayout)
        val yk = yOffset * k
        val h1 = heights.head * k
        val headVis = renderSVG(head, headLayout, h1).optTranslateY(yk.pixels)
        val (l, tailViss) = renderSequence(tail, headLayout.outEdge, oLayout * k, heights.tail.map(_ * k), yk + h1)
        val hv = if (l == 1) then headVis else headVis.scale(l)
        (k * l, hv :: tailViss)
      case Visualization.Sequence.ConsFlexiHead(head, tail) =>
        val (k, mLayout, tailViss) = renderSequenceBw(tail, oLayout, heights.tail, yOffset + heights.head)
        val headVis = renderSVG(head, IOLayout.Separate(iLayout * k, mLayout), heights.head * k).optTranslateY((yOffset * k).pixels)
        (k, headVis :: tailViss)
  }

  private def renderSequenceBw[X, Y](
    seq: Visualization.Sequence[X, Y],
    oLayout: EdgeLayout[Y],
    heights: List[Px],
    yOffset: Px,
  ): (Int, EdgeLayout[X], List[SVGElem]) = {
    require(heights.size == seq.size)

    seq match
      case Visualization.Sequence.TwoFlexiFst(fst, snd) =>
        ???
      case Visualization.Sequence.Two(fst, flexiSnd) =>
        // give the preferred layout to the first, non-flexi element
        val (k, fstLayout) = fst.ioProportions.layout(oLayout.pixelBreadth)
        val h1 = heights(0) * k
        val h2 = heights(1) * k
        val yk = yOffset * k
        val fstVis = renderSVG(fst, fstLayout, h1).optTranslateY(yk.pixels)
        val sndVis = renderSVG(flexiSnd, IOLayout.Separate(fstLayout.outEdge, oLayout * k), h2).translateY((yk + h1).pixels)
        (k, fstLayout.inEdge, List(fstVis, sndVis))
      case Visualization.Sequence.Cons(head, tail) =>
        ???
      case Visualization.Sequence.ConsFlexiHead(head, tail) =>
        ???
  }

  private def renderPar[∙[_, _], X1, X2, Y1, Y2](
    par: Visualization.Par[∙, X1, X2, Y1, Y2],
    edges: IOLayout[X1 ∙ X2, Y1 ∙ Y2],
    height: Px,
  ): SVGElem = {
    val Visualization.Par(op, a, b) = par
    val lStyle = AmbientStyle.leftOf(op)
    val rStyle = AmbientStyle.rightOf(op)
    edges match
      case IOLayout.Par(la, lb) =>
        val amb1 = renderAmbient(lStyle, la, height)
        val amb2 = renderAmbient(rStyle, lb, height).map(_.translate(la.pixelBreadth.pixels, 0.0))
        val ga = renderSVG(a, la, height)
        val gb = renderSVG(b, lb, height).translate(la.pixelBreadth.pixels, 0.0)
        SVGElem.Group(amb1 ++: amb2 ++: List(ga, gb))
      case other =>
        throw IllegalArgumentException(s"To render a Par, IOLayout.Par must be used. Was: $other")
  }

  private def renderConnectors[X, Y](
    connectors: List[Connector[X, Y] | TrapezoidArea[X, Y]],
    boundary: IOLayout[X, Y],
    height: Px,
  ): SVGElem =
    val (i, o) = boundary.separate
    renderConnectors(connectors, TrapezoidLayout(boundary, height))

  private def renderConnectors[X, Y](
    connectors: List[Connector[X, Y] | TrapezoidArea[X, Y]],
    layout: TrapezoidLayout[X, Y],
  ): SVGElem =
    SVGElem.Group(
      connectors.map(renderConnectorOrArea(_, layout)),
    )

  private def renderConnectorOrArea[I, O](
    connector: Connector[I, O] | TrapezoidArea[I, O],
    layout: TrapezoidLayout[I, O],
  ): SVGElem = {
    connector match
      case conn: Connector[I, O] =>
        renderConnector(conn, layout)
      case ta: TrapezoidArea[I, O] =>
        ta match
          case TrapezoidArea.Impl(src, tgt, fill) =>
            val srcCoords = layout.inSegmentCoords(src)
            val tgtCoords = layout.outSegmentCoords(tgt)
            curvyTrapezoid(srcCoords.x, srcCoords.width, tgtCoords.x, tgtCoords.width, layout.height, fill)
  }

  private def renderConnector[I, O](
    connector: Connector[I, O],
    layout: TrapezoidLayout[I, O],
  ): SVGElem = {
    val height = layout.height
    connector match
      case Connector.Across(src, tgt, Connector.Across.Style(fill, areaFill)) =>
        val srcCoords = layout.inWireCoords(src)
        val tgtCoords = layout.outWireCoords(tgt)
        val conn = curvyTrapezoid(srcCoords.wireX, srcCoords.wireWidth, tgtCoords.wireX, tgtCoords.wireWidth, height, fill)
        areaFill match {
          case None =>
            conn
          case Some(areaFill) =>
            val area = curvyTrapezoid(srcCoords.segmentX, srcCoords.segmentWidth, tgtCoords.segmentX, tgtCoords.segmentWidth, height, areaFill)
            SVGElem.Group(area, conn)
        }

      case Connector.LoopIn(src, tgt) =>
        import SVGElem.Path.Command.*

        val srcCoords = layout.inWireCoords(src)
        val tgtCoords = layout.inWireCoords(tgt)
        val sx1 = srcCoords.wireX
        val sw = srcCoords.wireWidth
        val sx2 = sx1 + sw
        val tx1 = tgtCoords.wireX
        val tw = tgtCoords.wireWidth
        val tx2 = tx1 + tw
        val ym = height.pixels / 2.0
        val yms = math.max(0.0, ym - sw.pixels)
        val ymt = math.max(0.0, ym - tw.pixels)
        val (sy1, sy2, ty1, ty2) =
          if (sx1 < tx1) // source to the left of target
            (ym, yms, ymt, ym)
          else
            (yms, ym, ym, ymt)
        SVGElem.Path(
          MoveTo(sx1, 0.px),
          CurveTo(sx1, sy1, tx2, ty2, tx2, 0.px),
          LineTo(tx1, 0.px),
          CurveTo(tx1, ty1, sx2, sy2, sx2, 0.px),
          Close,
        )

      case Connector.LoopOut(src, tgt) =>
        import SVGElem.Path.Command.*

        val srcCoords = layout.outWireCoords(src)
        val tgtCoords = layout.outWireCoords(tgt)
        val sx1 = srcCoords.wireX
        val sw = srcCoords.wireWidth
        val sx2 = sx1 + sw
        val tx1 = tgtCoords.wireX
        val tw = tgtCoords.wireWidth
        val tx2 = tx1 + tw
        val ym = height.pixels / 2.0
        val yms = math.min(height.pixels, ym + sw.pixels)
        val ymt = math.min(height.pixels, ym + tw.pixels)
        val (sy1, sy2, ty1, ty2) =
          if (sx1 < tx1) // source to the left of target
            (ym, yms, ymt, ym)
          else
            (yms, ym, ym, ymt)
        SVGElem.Path(
          MoveTo(sx1, height),
          CurveTo(sx1, sy1, tx2, ty2, tx2, height),
          LineTo(tx1, height),
          CurveTo(tx1, ty1, sx2, sy2, sx2, height),
          Close,
        )

      case Connector.StudIn(src) =>
        val H = 20
        val k =
          if (height.pixels >= H)
            1
          else
            math.ceil(H.toDouble / height.pixels).toInt

        val layK = layout * k
        val srcCoords = layK.inWireCoords(src)
        val (xi, wi) = (srcCoords.wireX, srcCoords.wireWidth)
        val ym = layK.height.pixels / 2
        val cx = xi + Px(wi.pixels / 2)
        val g =
          SVGElem.Group(
            SVGElem.Rect.solid(wi, ym.px, Color.Black).translate(xi.pixels, 0),
            SVGElem.Circle(
              radius = wi, // TODO: should take height into account
              fill = Some(Color.White),
              stroke = Some(Stroke(wi.pixels / 2.0, Color.Black)),
            ).translate(cx.pixels, ym)
          )
        if k == 1 then g else g.scale(1.0 / k)

      case Connector.StudOut(tgt) =>
        val H = 20
        val k =
          if (height.pixels >= H)
            1
          else
            math.ceil(H.toDouble / height.pixels).toInt

        val layK = layout * k
        val tgtCoords = layK.outWireCoords(tgt)
        val (xi, wi) = (tgtCoords.wireX, tgtCoords.wireWidth)
        val hk = layK.height
        val ym = hk.pixels / 2
        val cx = xi + Px(wi.pixels / 2)
        val g =
          SVGElem.Group(
            SVGElem.Rect.solid(wi, ym.px, Color.Black).translate(xi.pixels, hk.pixels - ym),
            SVGElem.Circle(
              radius = wi, // TODO: should take height into account
              fill = Some(Color.White),
              stroke = Some(Stroke(wi.pixels / 2.0, Color.Black)),
            ).translate(cx.pixels, hk.pixels - ym)
          )
        if k == 1 then g else g.scale(1.0 / k)

      case Connector.NoEntryOut(tgt) =>
        val EdgeLayout.WireCoords(segX, pre, w, post) = layout.outWireCoords(tgt)
        val x = segX + Px(math.max(0, pre.pixels - w.pixels))
        val w3 = Px(math.min(pre.pixels, w.pixels)) + w + Px(math.min(post.pixels, w.pixels))
        val h = Px(math.min((height.pixels + 2) / 3, w.pixels))
        val y = Px(height.pixels - h.pixels)
        SVGElem.Rect(x, y, w3, h, fill = Some(PredefinedFill.PatternRoadBlock), stroke = None, clipPath = Some(SVG.ClipPath.FillBox))
  }

  private def curvyTrapezoid[X, Y](
    reg: TrapezoidLayout[X, Y],
    fill: Color | PredefinedFill,
  ): SVGElem =
    val TrapezoidLayout(iOff, oOff, iLayout, oLayout, height) = reg
    curvyTrapezoid(iOff, iLayout.pixelBreadth, oOff, oLayout.pixelBreadth, height, fill)

  private def curvyTrapezoid(
    xi: Px,
    wi: Px,
    xo: Px,
    wo: Px,
    h: Px,
    fill: Color | PredefinedFill = Color.Black,
  ): SVGElem = {
    import SVGElem.Path.Command.*

    val xi2 = xi + wi
    val xo2 = xo + wo
    val ym: Double = h.pixels / 2.0
    SVGElem.Path(
      fill,
      MoveTo(xi, 0.px),
      CurveTo(xi, ym, xo, ym, xo, h),
      LineTo(xo2, h),
      CurveTo(xo2, ym, xi2, ym, xi2, 0.px),
      Close
    )
  }

  private def renderAmbient[X, Y](
    s: AmbientStyle,
    ioLayout: IOLayout[X, Y],
    height: Px,
  ): Option[SVGElem] =
    val (i, o) = ioLayout.separate
    renderAmbient(s, i, o, 0.px, 0.px, height)

  @deprecated
  private def renderAmbient[X, Y](
    s: AmbientStyle,
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): Option[SVGElem] =
    renderAmbient(s, EdgeSegment.pickId, EdgeSegment.pickId, iLayout, oLayout, iOffset, oOffset, height)

  private def renderAmbient[X, Y](
    s: AmbientStyle,
    reg: TrapezoidLayout[X, Y],
  ): Option[SVGElem] =
    renderAmbient(s, reg, EdgeSegment.pickId, EdgeSegment.pickId)

  @deprecated
  private def renderAmbient[X, Y](
    s: AmbientStyle,
    iSeg: EdgeSegment[?, X] | EdgeSegment.SubWire[X],
    oSeg: EdgeSegment[?, Y] | EdgeSegment.SubWire[Y],
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): Option[SVGElem] =
    renderAmbient(s, TrapezoidLayout(iOffset, oOffset, iLayout, oLayout, height), iSeg, oSeg)

  private def renderAmbient[X, Y](
    s: AmbientStyle,
    reg: TrapezoidLayout[X, Y],
    iSeg: EdgeSegment[?, X] | EdgeSegment.SubWire[X],
    oSeg: EdgeSegment[?, Y] | EdgeSegment.SubWire[Y],
  ): Option[SVGElem] = {
    val TrapezoidLayout(iOffset, oOffset, iLayout, oLayout, height) = reg
    val i = iLayout.segmentCoords(iSeg).offset(iOffset)
    val o = oLayout.segmentCoords(oSeg).offset(oOffset)
    renderAmbient(s, i, o, height)
  }

  private def renderAmbient[X, Y](
    s: AmbientStyle,
    i: EdgeLayout.SegmentCoords,
    o: EdgeLayout.SegmentCoords,
    height: Px,
  ): Option[SVGElem] = {
    val AmbientStyle(bg) = s
    bg map { curvyTrapezoid(i.x, i.width, o.x, o.width, height, _) }
  }

  private def renderAdapt[X, Y](
    m: Adaptoid[X, Y],
    reg: TrapezoidLayout[X, Y],
  ): SVGElem = {
    // hidden-by-default background for debugging purposes
    val hiddenBackground =
      curvyTrapezoid(reg, Color.Red)
        .debugOnly

    val content =
      m match
        case Adaptoid.Id(desc) =>
          renderIdentity(desc, reg)
        case Adaptoid.Expand(f) =>
          renderExpand(f, reg)
        case Adaptoid.Collapse(f) =>
          renderCollapse(f, reg)
        case p: Adaptoid.Par[op, x1, x2, y1, y2] =>
          val (reg1, reg2) = TrapezoidLayout.split[op, x1, x2, y1, y2](reg)
          val lStyle = AmbientStyle.leftOf(p.op)
          val rStyle = AmbientStyle.rightOf(p.op)
          val amb1 = renderAmbient(lStyle, reg1)
          val amb2 = renderAmbient(rStyle, reg2)
          val g1 = renderAdapt(p.f1, reg1)
          val g2 = renderAdapt(p.f2, reg2)
          SVGElem.Group(amb1 ++: amb2 ++: List(g1, g2))

    SVGElem.Group(hiddenBackground, content)
  }

  private def renderIdentity[X](
    x: EdgeDesc[X],
    reg: TrapezoidLayout[X, X],
  ): SVGElem =
    x match
      case EdgeDesc.SingleWire =>
        summon[X =:= Wire]
        renderConnector[Wire, Wire](
          Connector.Across(WirePick.pickId, WirePick.pickId),
          reg,
        )
      case x: EdgeDesc.Binary[op, x1, x2] =>
        summon[X =:= op[x1, x2]]
        val (reg1, reg2) = TrapezoidLayout.split[op, x1, x2, x1, x2](reg)
        val lStyle = AmbientStyle.leftOf(x.op)
        val rStyle = AmbientStyle.rightOf(x.op)
        val amb1 = renderAmbient(lStyle, reg1)
        val amb2 = renderAmbient(rStyle, reg2)
        val g1 = renderIdentity(x.x1, reg1)
        val g2 = renderIdentity(x.x2, reg2)
        SVGElem.Group(amb1 ++: amb2 ++: List(g1, g2))

  private def renderFanOutOrId[Y](
    y: EdgeDesc[Y],
    reg: TrapezoidLayout[Wire, Y],
  ): SVGElem =
    y match
      case EdgeDesc.SingleWire =>
        summon[Y =:= Wire]
        renderIdentity[Wire](EdgeDesc.SingleWire, reg)
      case p: EdgeDesc.Binary[op, y1, y2] =>
        renderFanOut(p, reg)

  private def renderFanOut[∙[_, _], Y1, Y2](
    y: EdgeDesc.Binary[∙, Y1, Y2],
    reg: TrapezoidLayout[Wire, Y1 ∙ Y2],
  ): SVGElem = {
    val lStyle = AmbientStyle.leftOf(y.op)
    val rStyle = AmbientStyle.rightOf(y.op)
    val c1 = Connector.Across[Wire, Wire ∙ Wire](WirePick.pickId, WirePick.pickL)
    val c2 = Connector.Across[Wire, Wire ∙ Wire](WirePick.pickId, WirePick.pickR)
    (y.x1, y.x2) match {
      case (EdgeDesc.SingleWire, EdgeDesc.SingleWire) =>
        summon[Y1 =:= Wire]
        summon[Y2 =:= Wire]
        val amb1 = renderAmbient(lStyle, reg, EdgeSegment.pickId.wireLHalf, EdgeSegment.pickL)
        val amb2 = renderAmbient(rStyle, reg, EdgeSegment.pickId.wireRHalf, EdgeSegment.pickR)
        val g1 = renderConnector(c1, reg)
        val g2 = renderConnector(c2, reg)
        SVGElem.Group(amb1 ++: amb2 ++: List(g1, g2))
      case _ =>
        val (o1, o2) = EdgeLayout.split(reg.oLayout)
        val (i1, w1) = EdgeProportions.unitSize.layout(o1.pixelBreadth)
        val (i2, w2) = EdgeProportions.unitSize.layout(o2.pixelBreadth)
        val (ki1, ki2, k) = leastCommonMultiple(i1, i2)
        val regK = reg * k
        val wk = EdgeLayout.Par[∙, Wire, Wire](w1 * ki1, w2 * ki2)
        regK.vsplit(wk)(
          Length.one,
          Length.max(y.x1.depth, y.x2.depth)
        ) match
          case (l, iReg, oReg) =>
            val (oReg1, oReg2) = TrapezoidLayout.split(oReg)
            val h1 = iReg.height.pixels
            val amb1 = renderAmbient(lStyle, iReg, EdgeSegment.pickId.wireLHalf, EdgeSegment.pickL)
            val amb2 = renderAmbient(rStyle, iReg, EdgeSegment.pickId.wireRHalf, EdgeSegment.pickR)
            val g1 = renderConnector(c1, iReg)
            val g2 = renderConnector(c2, iReg)
            val amb3 = renderAmbient(lStyle, oReg1).map(_.translate(0, h1))
            val amb4 = renderAmbient(rStyle, oReg2).map(_.translate(0, h1))
            val g3 = renderFanOutOrId(y.x1, oReg1).translate(0, h1)
            val g4 = renderFanOutOrId(y.x2, oReg2).translate(0, h1)
            val g = SVGElem.Group(amb1 ++: amb2 ++: amb3 ++: amb4 ++: List(g1, g2, g3, g4))
            if (k * l == 1) g else g.scale(1.0/(k*l))
    }
  }

  private def renderFanInOrId[X](
    x: EdgeDesc[X],
    reg: TrapezoidLayout[X, Wire],
  ): SVGElem =
    x match
      case EdgeDesc.SingleWire =>
        summon[X =:= Wire]
        renderIdentity[Wire](EdgeDesc.SingleWire, reg)
      case p: EdgeDesc.Binary[op, x1, x2] =>
        renderFanIn(p, reg)

  private def renderFanIn[∙[_, _], X1, X2](
    x: EdgeDesc.Binary[∙, X1, X2],
    reg: TrapezoidLayout[X1 ∙ X2, Wire],
  ): SVGElem = {
    val lStyle = AmbientStyle.leftOf(x.op)
    val rStyle = AmbientStyle.rightOf(x.op)
    val c1 = Connector.Across[Wire ∙ Wire, Wire](WirePick.pickL, WirePick.pickId)
    val c2 = Connector.Across[Wire ∙ Wire, Wire](WirePick.pickR, WirePick.pickId)
    (x.x1, x.x2) match {
      case (EdgeDesc.SingleWire, EdgeDesc.SingleWire) =>
        summon[X1 =:= Wire]
        summon[X2 =:= Wire]
        val amb1 = renderAmbient(lStyle, reg, EdgeSegment.pickL, EdgeSegment.pickId.wireLHalf)
        val amb2 = renderAmbient(rStyle, reg, EdgeSegment.pickR, EdgeSegment.pickId.wireRHalf)
        val g1 = renderConnector(c1, reg)
        val g2 = renderConnector(c2, reg)
        SVGElem.Group(amb1 ++: amb2 ++: List(g1, g2))
      case _ =>
        val (i1, i2) = EdgeLayout.split(reg.iLayout)
        val (j1, w1) = EdgeProportions.unitSize.layout(i1.pixelBreadth)
        val (j2, w2) = EdgeProportions.unitSize.layout(i2.pixelBreadth)
        val (kj1, kj2, k) = leastCommonMultiple(j1, j2)
        val regK = reg * k
        val wk = EdgeLayout.Par[∙, Wire, Wire](w1 * kj1, w2 * kj2)
        regK.vsplit(wk)(
          Length.max(x.x1.depth, x.x2.depth),
          Length.one,
        ) match
          case (l, iReg, oReg) =>
            val (iReg1, iReg2) = TrapezoidLayout.split(iReg)
            val h1 = iReg.height.pixels
            val amb1 = renderAmbient(lStyle, oReg, EdgeSegment.pickL, EdgeSegment.pickId.wireLHalf).map(_.translate(0, h1))
            val amb2 = renderAmbient(rStyle, oReg, EdgeSegment.pickR, EdgeSegment.pickId.wireRHalf).map(_.translate(0, h1))
            val g1 = renderConnector(c1, oReg).translate(0, h1)
            val g2 = renderConnector(c2, oReg).translate(0, h1)
            val amb3 = renderAmbient(lStyle, iReg1)
            val amb4 = renderAmbient(rStyle, iReg2)
            val g3 = renderFanInOrId(x.x1, iReg1)
            val g4 = renderFanInOrId(x.x2, iReg2)
            val g = SVGElem.Group(amb1 ++: amb2 ++: amb3 ++: amb4 ++: List(g1, g2, g3, g4))
            if (k * l == 1) g else g.scale(1.0/(k*l))
    }
  }

  private def renderExpand[X, Y](
    f: X IsRefinedBy Y,
    reg: TrapezoidLayout[X, Y],
  ): SVGElem =
    f match
      case IsRefinedBy.Id(desc) =>
        renderIdentity(desc, reg)
      case IsRefinedBy.Initial(outDesc) =>
        renderFanOutOrId(outDesc, reg)
      case p: IsRefinedBy.Pairwise[op, x1, x2, y1, y2] =>
        summon[X =:= op[x1, x2]]
        summon[Y =:= op[y1, y2]]
        val (reg1, reg2) = TrapezoidLayout.split[op, x1, x2, y1, y2](reg)
        val lStyle = AmbientStyle.leftOf(p.op)
        val rStyle = AmbientStyle.rightOf(p.op)
        val amb1 = renderAmbient(lStyle, reg1)
        val amb2 = renderAmbient(rStyle, reg2)
        val g1 = renderExpand(p.f1, reg1)
        val g2 = renderExpand(p.f2, reg2)
        SVGElem.Group(amb1 ++: amb2 ++: List(g1, g2))

  private def renderCollapse[X, Y](
    f: Y IsRefinedBy X,
    reg: TrapezoidLayout[X, Y],
  ): SVGElem =
    f match
      case IsRefinedBy.Id(desc) =>
        renderIdentity(desc, reg)
      case IsRefinedBy.Initial(x) =>
        summon[Y =:= Wire]
        renderFanInOrId(x, reg)
      case p: IsRefinedBy.Pairwise[op, y1, y2, x1, x2] =>
        summon[X =:= op[x1, x2]]
        summon[Y =:= op[y1, y2]]
        val (reg1, reg2) = TrapezoidLayout.split[op, x1, x2, y1, y2](reg)
        val lStyle = AmbientStyle.leftOf(p.op)
        val rStyle = AmbientStyle.rightOf(p.op)
        val amb1 = renderAmbient(lStyle, reg1)
        val amb2 = renderAmbient(rStyle, reg2)
        val g1 = renderCollapse(p.f1, reg1)
        val g2 = renderCollapse(p.f2, reg2)
        SVGElem.Group(amb1 ++: amb2 ++: List(g1, g2))

  private def scaleToFit(srcW: Int, srcH: Int, tgtW: Int, tgtH: Int): Double =
    require(srcW >  0)
    require(srcH >  0)
    require(tgtW >= 0)
    require(tgtH >= 0)
    val scaleW = tgtW.toDouble / srcW
    val scaleH = tgtH.toDouble / srcH
    math.min(scaleW, scaleH)
}