package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.Color
import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.examples.workflow.generic.vis.Px.*
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily.{Monospace, Serif}
import libretto.lambda.examples.workflow.generic.vis.SVG.{Stroke, TextAnchor}
import libretto.lambda.examples.workflow.generic.vis.util.{IntegralProportions, leastCommonMultiple}

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
      case seq: Visualization.Seq[x, y1, y2, z] =>
        renderSeq(seq, edges, height)
      case par: Visualization.Par[bin, x1, x2, y1, y2] =>
        renderPar(par, edges, height)
      case Visualization.ConnectorsOverlay(base, connectors) =>
        val conns = renderConnectors(connectors, edges, height)
        base match
          case Left(vis) =>
            val v = renderSVG(vis, edges, height)
            SVGElem.Group(v, conns)
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

  private def renderSeq[X, Y1, Y2, Z](
    seq: Visualization.Seq[X, Y1, Y2, Z],
    edges: IOLayout[X, Z],
    height: Px,
  ): SVGElem =
    val Visualization.Seq(a, m, b) = seq

    val (layoutX, layoutZ) = edges.separate
    val ioA = a.ioProportions
    val ioB = b.ioProportions

    val (i, layoutA) = ioA.layoutFw(layoutX)
    val (j, layoutB) = ioB.layoutBw(layoutZ)

    val (ki, kj, k) = leastCommonMultiple(i, j)

    val layoutAk = layoutA * ki
    val layoutBk = layoutB * kj
    val layoutY1 = layoutAk.outEdge
    val layoutY2 = layoutBk.inEdge

    Length.divideProportionally((height * k).pixels)(a.length, m.length, b.length) match
      case IntegralProportions(l, sizes) =>
        val List(ha, hm, hb) = sizes
        val g = SVGElem.Group(
          renderSVG(a, layoutAk * l, Px(ha)),
          renderMorph(m, layoutY1 * l, layoutY2 * l, 0.px, 0.px, Px(hm)).translate(0.0, ha),
          renderSVG(b, layoutBk * l, Px(hb)).translate(0.0, ha + hm),
        )
        if (k * l == 1) then g else g.scale(1.0/(k*l))
  end renderSeq

  private def renderPar[∙[_, _], X1, X2, Y1, Y2](
    par: Visualization.Par[∙, X1, X2, Y1, Y2],
    edges: IOLayout[X1 ∙ X2, Y1 ∙ Y2],
    height: Px,
  ): SVGElem =
    val Visualization.Par(a, b) = par
    edges match
      case IOLayout.Par(la, lb) =>
        val ga = renderSVG(a, la, height)
        val gb = renderSVG(b, lb, height)
        SVGElem.Group(ga, gb.translate(la.pixelBreadth.pixels, 0.0))
      case other =>
        throw IllegalArgumentException(s"To render a Par, IOLayout.Par must be used. Was: $other")
  end renderPar

  private def renderConnectors[X, Y](
    connectors: List[Connector[X, Y]],
    boundary: IOLayout[X, Y],
    height: Px,
  ): SVGElem =
    val (inEdge, outEdge) = boundary.separate
    SVGElem.Group(
      connectors.map(renderConnector(_, inEdge, outEdge, 0.px, 0.px, height)),
    )

  private def renderConnector[I, O](
    connector: Connector[I, O],
    inEdge: EdgeLayout[I],
    outEdge: EdgeLayout[O],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem = {
    println(s"renderConnector into ${inEdge.pixelBreadth} x $height")
    import SVGElem.Path.Command.*

    connector match
      case Connector.Across(src, tgt, Connector.Style(color)) =>
        val (xi, wi) = inEdge.coordsOf(src)
        val (xo, wo) = outEdge.coordsOf(tgt)
        curvyTrapezoid(iOffset + xi, wi, oOffset + xo, wo, height, color)

      case Connector.StudIn(src, Connector.Style(color)) =>
        val H = 20
        val k =
          if (height.pixels >= H)
            1
          else
            math.ceil(H.toDouble / height.pixels).toInt

        println(s"render StudIn($src) into ${inEdge.pixelBreadth} x $height, k = $k")

        val (xi, wi) = (inEdge * k).coordsOf(src)
        val xi1 = iOffset * k + xi
        val ym = (height * k).pixels / 2
        val cx = xi1 + Px(wi.pixels / 2)
        val g =
          SVGElem.Group(
            SVGElem.Rect.solid(wi, ym.px, color).translate(xi1.pixels, 0),
            SVGElem.Circle(
              radius = wi, // TODO: should take height into account
              fill = Some(Color.White),
              stroke = Some(Stroke(wi.pixels / 2.0, color)),
            ).translate(cx.pixels, ym)
          )
        if k == 1 then g else g.scale(1.0 / k)

      case Connector.StudOut(tgt, Connector.Style(color)) =>
        val H = 20
        val k =
          if (height.pixels >= H)
            1
          else
            math.ceil(H.toDouble / height.pixels).toInt

        println(s"render StudOut($tgt) into ${outEdge.pixelBreadth} x $height, k = $k")

        val (xi, wi) = (outEdge * k).coordsOf(tgt)
        val xi1 = oOffset * k + xi
        val hk = height * k
        val ym = hk.pixels / 2
        val cx = xi1 + Px(wi.pixels / 2)
        val g =
          SVGElem.Group(
            SVGElem.Rect.solid(wi, ym.px, color).translate(xi1.pixels, hk.pixels - ym),
            SVGElem.Circle(
              radius = wi, // TODO: should take height into account
              fill = Some(Color.White),
              stroke = Some(Stroke(wi.pixels / 2.0, color)),
            ).translate(cx.pixels, hk.pixels - ym)
          )
        if k == 1 then g else g.scale(1.0 / k)
  }

  private def curvyTrapezoid(
    xi: Px,
    wi: Px,
    xo: Px,
    wo: Px,
    h: Px,
    fill: Color | ColorGradient = Color.Black,
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

  private def renderMorph[X, Y](
    m: Morph[X, Y],
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem = {
    // hidden background for debugging purposes
    val hiddenBackground =
      curvyTrapezoid(iOffset, iLayout.pixelBreadth, oOffset, oLayout.pixelBreadth, height, Color.Red)
        .hidden

    val content =
      m match
        case Morph.Id(desc) =>
          renderIdentity(desc, iLayout, oLayout, iOffset, oOffset, height)
        case Morph.Refine(f) =>
          renderRefine(f, iLayout, oLayout, iOffset, oOffset, height)
        case Morph.Unrefine(f) =>
          renderUnrefine(f, iLayout, oLayout, iOffset, oOffset, height)
        case p: Morph.Par[op, x1, x2, y1, y2] =>
          val (i1, i2) = EdgeLayout.split[op, x1, x2](iLayout)
          val (o1, o2) = EdgeLayout.split[op, y1, y2](oLayout)
          val g1 = renderMorph(p.f1, i1, o1, iOffset, oOffset, height)
          val g2 = renderMorph(p.f2, i2, o2, iOffset + i1.pixelBreadth, oOffset + o1.pixelBreadth, height)
          SVGElem.Group(g1, g2)

    SVGElem.Group(hiddenBackground, content)
  }

  private def renderIdentity[X](
    x: EdgeDesc[X],
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[X],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem =
    x match
      case EdgeDesc.SingleWire =>
        summon[X =:= Wire]
        renderConnector[Wire, Wire](
          Connector.Across(WirePick.Id, WirePick.Id),
          iLayout,
          oLayout,
          iOffset,
          oOffset,
          height,
        )
      case x: EdgeDesc.Binary[op, x1, x2] =>
        summon[X =:= op[x1, x2]]
        val (i1, i2) = EdgeLayout.split[op, x1, x2](iLayout)
        val (o1, o2) = EdgeLayout.split[op, x1, x2](oLayout)
        val g1 = renderIdentity(x.x1, i1, o1, iOffset, oOffset, height)
        val g2 = renderIdentity(x.x2, i2, o2, iOffset + i1.pixelBreadth, oOffset + o1.pixelBreadth, height)
        SVGElem.Group(g1, g2)

  private def renderFanOutOrId[Y](
    y: EdgeDesc[Y],
    iLayout: EdgeLayout[Wire],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem =
    y match
      case EdgeDesc.SingleWire =>
        summon[Y =:= Wire]
        renderConnector[Wire, Wire](
          Connector.Across(WirePick.Id, WirePick.Id),
          iLayout,
          oLayout,
          iOffset,
          oOffset,
          height,
        )
      case p: EdgeDesc.Binary[op, y1, y2] =>
        renderFanOut(p, iLayout, oLayout, iOffset, oOffset, height)

  private def renderFanOut[∙[_, _], Y1, Y2](
    y: EdgeDesc.Binary[∙, Y1, Y2],
    iLayout: EdgeLayout[Wire],
    oLayout: EdgeLayout[Y1 ∙ Y2],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem = {
    println(s"renderFanOut into ${iLayout.pixelBreadth} x $height")
    val c1 = Connector.Across[Wire, Wire ∙ Wire](WirePick.Id, WirePick.pickL)
    val c2 = Connector.Across[Wire, Wire ∙ Wire](WirePick.Id, WirePick.pickR)
    val (o1, o2) = EdgeLayout.split(oLayout)
    val (i1, w1) = EdgeProportions.unitSize.layout(o1.pixelBreadth)
    val (i2, w2) = EdgeProportions.unitSize.layout(o2.pixelBreadth)
    val (ki1, ki2, k) = leastCommonMultiple(i1, i2)
    (y.x1, y.x2) match {
      case (EdgeDesc.SingleWire, EdgeDesc.SingleWire) =>
        summon[Y1 =:= Wire]
        summon[Y2 =:= Wire]
        val g1 = renderConnector(c1, iLayout * k, oLayout * k, iOffset * k, oOffset * k, height)
        val g2 = renderConnector(c2, iLayout * k, oLayout * k, iOffset * k, oOffset * k, height)
        val g = SVGElem.Group(g1, g2)
        if k == 1 then g else g.scale(1.0 / k)
      case _ =>
        Length.divideProportionally((height * k).pixels)(
          Length.one,
          Length.max(y.x1.depth, y.x2.depth)
        ) match
          case IntegralProportions(l, List(h1, h2)) =>
            val ikl = iLayout * k * l
            val wl1 = w1 * ki1 * l
            val wl2 = w2 * ki2 * l
            val wl = EdgeLayout.Par[∙, Wire, Wire](wl1, wl2)
            val y1 = o1 * k * l
            val y2 = o2 * k * l
            val iOff = iOffset * k * l
            val oOff = oOffset * k * l
            val mOff = Px((iOff * h1 + oOff * h2).pixels / (h1 + h2))
            val g1 = renderConnector(c1, ikl, wl, iOff, mOff, h1.px)
            val g2 = renderConnector(c2, ikl, wl, iOff, mOff, h1.px)
            val g3 = renderFanOutOrId(y.x1, wl1, y1, mOff, oOff, h2.px).translate(0, h1)
            val g4 = renderFanOutOrId(y.x2, wl2, y2, mOff + wl1.pixelBreadth, oOff + y1.pixelBreadth, h2.px).translate(0, h1)
            val g = SVGElem.Group(g1, g2, g3, g4)
            if (k * l == 1) g else g.scale(1.0/(k*l))
    }
  }

  private def renderFanInOrId[X](
    x: EdgeDesc[X],
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Wire],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem =
    x match
      case EdgeDesc.SingleWire =>
        summon[X =:= Wire]
        renderConnector[Wire, Wire](
          Connector.Across(WirePick.Id, WirePick.Id),
          iLayout,
          oLayout,
          iOffset,
          oOffset,
          height,
        )
      case p: EdgeDesc.Binary[op, x1, x2] =>
        renderFanIn(p, iLayout, oLayout, iOffset, oOffset, height)

  private def renderFanIn[∙[_, _], X1, X2](
    x: EdgeDesc.Binary[∙, X1, X2],
    iLayout: EdgeLayout[X1 ∙ X2],
    oLayout: EdgeLayout[Wire],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem = {
    println(s"renderFanIn into ${iLayout.pixelBreadth} x $height")
    val c1 = Connector.Across[Wire ∙ Wire, Wire](WirePick.pickL, WirePick.Id)
    val c2 = Connector.Across[Wire ∙ Wire, Wire](WirePick.pickR, WirePick.Id)
    val (i1, i2) = EdgeLayout.split(iLayout)
    val (j1, w1) = EdgeProportions.unitSize.layout(i1.pixelBreadth)
    val (j2, w2) = EdgeProportions.unitSize.layout(i2.pixelBreadth)
    val (kj1, kj2, k) = leastCommonMultiple(j1, j2)
    (x.x1, x.x2) match {
      case (EdgeDesc.SingleWire, EdgeDesc.SingleWire) =>
        summon[X1 =:= Wire]
        summon[X2 =:= Wire]
        val g1 = renderConnector(c1, iLayout * k, oLayout * k, iOffset * k, oOffset * k, height)
        val g2 = renderConnector(c2, iLayout * k, oLayout * k, iOffset * k, oOffset * k, height)
        val g = SVGElem.Group(g1, g2)
        if k == 1 then g else g.scale(1.0 / k)
      case _ =>
        Length.divideProportionally((height * k).pixels)(
          Length.max(x.x1.depth, x.x2.depth),
          Length.one,
        ) match
          case IntegralProportions(l, List(h1, h2)) =>
            val okl = oLayout * k * l
            val wl1 = w1 * kj1 * l
            val wl2 = w2 * kj2 * l
            val wl = EdgeLayout.Par[∙, Wire, Wire](wl1, wl2)
            val x1 = i1 * k * l
            val x2 = i2 * k * l
            val iOff = iOffset * k * l
            val oOff = oOffset * k * l
            val mOff = Px((iOff * h1 + oOff * h2).pixels / (h1 + h2))
            val g1 = renderConnector(c1, wl, okl, mOff, oOff, h2.px).translate(0, h1)
            val g2 = renderConnector(c2, wl, okl, mOff, oOff, h2.px).translate(0, h1)
            val g3 = renderFanInOrId(x.x1, x1, wl1, iOff, mOff, h1.px)
            val g4 = renderFanInOrId(x.x2, x2, wl2, iOff + x1.pixelBreadth, mOff + wl1.pixelBreadth, h1.px)
            val g = SVGElem.Group(g1, g2, g3, g4)
            if (k * l == 1) g else g.scale(1.0/(k*l))
    }
  }

  private def renderRefine[X, Y](
    f: X IsRefinedBy Y,
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem =
    println(s"renderRefine into ${iLayout.pixelBreadth} x $height")
    f match
      case IsRefinedBy.Id(desc) =>
        renderIdentity(desc, iLayout, oLayout, iOffset, oOffset, height)
      case IsRefinedBy.Initial(outDesc) =>
        renderFanOutOrId(outDesc, iLayout, oLayout, iOffset, oOffset, height)
      case p: IsRefinedBy.Pairwise[op, x1, x2, y1, y2] =>
        summon[X =:= op[x1, x2]]
        summon[Y =:= op[y1, y2]]
        val (i1, i2) = EdgeLayout.split[op, x1, x2](iLayout)
        val (o1, o2) = EdgeLayout.split[op, y1, y2](oLayout)
        val g1 = renderRefine(p.f1, i1, o1, iOffset, oOffset, height)
        val g2 = renderRefine(p.f2, i2, o2, iOffset + i1.pixelBreadth, oOffset + o1.pixelBreadth, height)
        SVGElem.Group(g1, g2)

  private def renderUnrefine[X, Y](
    f: Y IsRefinedBy X,
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem =
    println(s"renderUnrefine into ${iLayout.pixelBreadth} x $height")
    f match
      case IsRefinedBy.Id(desc) =>
        renderIdentity(desc, iLayout, oLayout, iOffset, oOffset, height)
      case IsRefinedBy.Initial(x) =>
        summon[Y =:= Wire]
        renderFanInOrId(x, iLayout, oLayout, iOffset, oOffset, height)
      case p: IsRefinedBy.Pairwise[op, y1, y2, x1, x2] =>
        summon[X =:= op[x1, x2]]
        summon[Y =:= op[y1, y2]]
        val (i1, i2) = EdgeLayout.split[op, x1, x2](iLayout)
        val (o1, o2) = EdgeLayout.split[op, y1, y2](oLayout)
        val g1 = renderUnrefine(p.f1, i1, o1, iOffset, oOffset, height)
        val g2 = renderUnrefine(p.f2, i2, o2, iOffset + i1.pixelBreadth, oOffset + o1.pixelBreadth, height)
        SVGElem.Group(g1, g2)

  private def scaleToFit(srcW: Int, srcH: Int, tgtW: Int, tgtH: Int): Double =
    require(srcW >  0)
    require(srcH >  0)
    require(tgtW >= 0)
    require(tgtH >= 0)
    val scaleW = tgtW.toDouble / srcW
    val scaleH = tgtH.toDouble / srcH
    math.min(scaleW, scaleH)
}