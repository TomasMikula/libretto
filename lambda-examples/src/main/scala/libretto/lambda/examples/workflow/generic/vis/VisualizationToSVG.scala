package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.examples.workflow.generic.vis.Px.*
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily.Monospace
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
      case Visualization.Unimplemented(label) =>
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
      SVGElem.RectOutline(width, height, math.min(width.pixels / 20.0, height.pixels / 20.0), "red"),
      text.scale(scale)
    )

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
      case IOLayout.Unimplemented(width) =>
        Breadth.divideProportionally(width.pixels)(a.breadth, b.breadth) match
          case IntegralProportions(k, sizes) =>
            val List(wa, wb) = sizes
            val (i, la) = a.ioProportions.layout(Px(wa))
            val (j, lb) = b.ioProportions.layout(Px(wb))
            val (_, _, k2) = leastCommonMultiple(i, j)
            val g = SVGElem.Group(
              renderSVG(a, la, height * k * k2),
              renderSVG(b, lb, height * k * k2).translate(la.pixelBreadth.pixels, 0.0),
            )
            if (k * k2 == 1) then g else g.scale(1.0/(k*k2))
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
    import SVGElem.Path.Command.*

    connector match
      case Connector.Across(src, tgt) =>
        val (xi, wi) = inEdge.coordsOf(src)
        val (xo, wo) = outEdge.coordsOf(tgt)
        val xi1 = iOffset + xi
        val xi2 = xi1 + wi
        val xo1 = oOffset + xo
        val xo2 = xo1 + wo
        val ym: Double = height.pixels / 2.0
        SVGElem.Path(
          MoveTo(xi1, 0.px),
          CurveTo(xi1, ym, xo1, ym, xo1, height),
          LineTo(xo2, height),
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
  ): SVGElem =
    m match
      case Morph.Id(desc) =>
        renderIdentity(desc, iLayout, oLayout, iOffset, oOffset, height)
      case Morph.Refine(f) =>
        renderRefine(f, iLayout, oLayout, iOffset, oOffset, height)
      case Morph.Unrefine(f) =>
        renderUnimplemented(s"Morph.${m.getClass.getSimpleName}", iLayout.pixelBreadth, height)
          .translate(iOffset.pixels, 0.0)
      case p: Morph.Par[op, x1, x2, y1, y2] =>
        val (i1, i2) = EdgeLayout.split[op, x1, x2](iLayout)
        val (o1, o2) = EdgeLayout.split[op, y1, y2](oLayout)
        val g1 = renderMorph(p.f1, i1, o1, iOffset, oOffset, height)
        val g2 = renderMorph(p.f2, i2, o2, iOffset + i1.pixelBreadth, oOffset + o1.pixelBreadth, height)
        SVGElem.Group(g1, g2)

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

  private def renderFanOut[Y](
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
        summon[Y =:= op[y1, y2]]
        val (o1, o2) = EdgeLayout.split[op, y1, y2](oLayout)
        val (i1, w1) = EdgeProportions.unitWire.layout(o1.pixelBreadth)
        val (i2, w2) = EdgeProportions.unitWire.layout(o2.pixelBreadth)
        val (ki1, ki2, k) = leastCommonMultiple(i1, i2)
        Length.divideProportionally((height * k).pixels)(
          Length.one,
          Length.max(p.x1.depth, p.x2.depth)
        ) match
          case IntegralProportions(l, List(h1, h2)) =>
            val ikl = iLayout * k * l
            val wl1 = w1 * ki1 * l
            val wl2 = w2 * ki2 * l
            val wl = EdgeLayout.Par[op, Wire, Wire](wl1, wl2)
            val y1 = o1 * k * l
            val y2 = o2 * k * l
            val iOff = iOffset * k * l
            val oOff = oOffset * k * l
            val mOff = Px((iOff * h1 + oOff * h2).pixels / (h1 + h2))
            val c1 = Connector.Across[Wire, op[Wire, Wire]](WirePick.Id, WirePick.pickL)
            val c2 = Connector.Across[Wire, op[Wire, Wire]](WirePick.Id, WirePick.pickR)
            val g1 = renderConnector(c1, ikl, wl, iOff, mOff, h1.px)
            val g2 = renderConnector(c2, ikl, wl, iOff, mOff, h1.px)
            val g3 = renderFanOut(p.x1, wl1, y1, mOff, oOff, h2.px).translate(0, h1)
            val g4 = renderFanOut(p.x2, wl2, y2, mOff + wl1.pixelBreadth, oOff + y1.pixelBreadth, h2.px).translate(0, h1)
            val g = SVGElem.Group(g1, g2, g3, g4)
            if (k * l == 1) g else g.scale(1.0/(k*l))

  private def renderRefine[X, Y](
    f: IsRefinedBy[X, Y],
    iLayout: EdgeLayout[X],
    oLayout: EdgeLayout[Y],
    iOffset: Px,
    oOffset: Px,
    height: Px,
  ): SVGElem =
    f match
      case IsRefinedBy.Id(desc) =>
        renderIdentity(desc, iLayout, oLayout, iOffset, oOffset, height)
      case IsRefinedBy.Initial(outDesc) =>
        renderFanOut(outDesc, iLayout, oLayout, iOffset, oOffset, height)
      case p: IsRefinedBy.Pairwise[op, x1, x2, y1, y2] =>
        summon[X =:= op[x1, x2]]
        summon[Y =:= op[y1, y2]]
        val (i1, i2) = EdgeLayout.split[op, x1, x2](iLayout)
        val (o1, o2) = EdgeLayout.split[op, y1, y2](oLayout)
        val g1 = renderRefine(p.f1, i1, o1, iOffset, oOffset, height)
        val g2 = renderRefine(p.f2, i2, o2, iOffset + i1.pixelBreadth, oOffset + o1.pixelBreadth, height)
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