package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.examples.workflow.generic.vis.Dimensions.*
import libretto.lambda.examples.workflow.generic.vis.SVG.*
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily.Monospace

object VisualizationToSVG {
  def renderSVGToFit(g: Visualization[?, ?], W: Int, H: Int): SVG =
    val r = g.aspectRatio
    val (w, h) = r.scaleToFit(W, H)

    renderSVG(g, Px(w), Px(h))

  def renderSVG(g: Visualization[?, ?], width: Px, height: Px): SVG =
    println(s"rendering ${g.getClass.getSimpleName} into $width x $height")
    g match
      case seq: Visualization.Seq[x, y1, y2, z] =>
        renderSeq(seq, width, height)
      case par: Visualization.Par[bin, x1, x2, y1, y2] =>
        renderPar(par, width, height)
      case Visualization.Merge() =>
        renderSVG(Visualization.Unimplemented("Merge"), width, height)
      case Visualization.Unimplemented(label) =>
        val text = SVG.Text(label, x = 0.px, y = 20.px, Monospace, fontSize = 20.px)
        val textH = text.fontSize.pixels
        val textW = (label.length * textH * 3 + 4) / 5 // XXX: just a guess that character width is 3/5 of font size
        val scale =
          height.pixels match
            case 0      => 0.0
            case height => scaleToFit(textW, textH, width.pixels, height).toDouble
        SVG.Group(
          SVG.RectOutline(width, height, math.min(width.pixels / 20.0, height.pixels / 20.0), "red"),
          text.scale(scale)
        )

  private def renderSeq[X, Y1, Y2, Z](seq: Visualization.Seq[X, Y1, Y2, Z], width: Px, height: Px): SVG =
    val Visualization.Seq(a, m, b) = seq
    // XXX: unused m
    Length.divideProportionally(height.pixels)(a.length, b.length) match
      case IntegralProportions(k, sizes) =>
        val List(ha, hb) = sizes
        val g = SVG.Group(
          renderSVG(a, width * k, Px(ha)),
          renderSVG(b, width * k, Px(hb)).translate(0.0, ha),
        )
        if (k == 1) then g else g.scale(1.0/k)
  end renderSeq

  private def renderPar[∙[_, _], X1, X2, Y1, Y2](par: Visualization.Par[∙, X1, X2, Y1, Y2], width: Px, height: Px): SVG =
    val Visualization.Par(a, b) = par
    Breadth.divideProportionally(width.pixels)(a.breadth, b.breadth) match
      case IntegralProportions(k, sizes) =>
        val List(wa, wb) = sizes
        val g = SVG.Group(
          renderSVG(a, Px(wa), height * k),
          renderSVG(b, Px(wb), height * k).translate(wa, 0.0),
        )
        if (k == 1) then g else g.scale(1.0/k)
  end renderPar

  private def scaleToFit(srcW: Int, srcH: Int, tgtW: Int, tgtH: Int): Double =
    require(srcW >  0)
    require(srcH >  0)
    require(tgtW >= 0)
    require(tgtH >= 0)
    val scaleW = tgtW.toDouble / srcW
    val scaleH = tgtH.toDouble / srcH
    math.min(scaleW, scaleH)
}