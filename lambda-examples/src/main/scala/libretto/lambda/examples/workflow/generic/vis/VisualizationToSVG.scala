package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.DefaultDimensions.*
import libretto.lambda.examples.workflow.generic.vis.Dimensions.*
import libretto.lambda.examples.workflow.generic.vis.SVG.*
import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily.Monospace

object VisualizationToSVG {
  private val W = 640
  private val H = 480

  /** Render to a default bounding rectangle. */
  def renderSVG(g: Visualization): SVG =
    val r = g.aspectRatio
    val (w, h) = r.scaleToFit(W, H)

    renderSVG(g, Px(w), Px(h))

  def renderSVG(g: Visualization, width: Px, height: Px): SVG =
    println(s"rendering into $width x $height")
    g match
      case seq: Visualization.Seq =>
        renderSeq(seq, width, height)
      case par: Visualization.Par =>
        renderPar(par, width, height)
      case Visualization.Unimplemented(label) =>
        val text = SVG.Text(label, x = 0.px, y = 20.px, Monospace, fontSize = 20.px)
        val textH = text.fontSize.pixels
        val textW = (label.length * textH * 3 + 4) / 5 // XXX: just a guess that character width is 3/5 of font size
        val scale =
          height.pixels match
            case 0      => 0.0
            case height => scaleToFit(textW, textH, width.pixels, height).toDouble
        SVG.Transformed(text, SVG.Transform.Scale(scale))

  private def renderSeq(seq: Visualization.Seq, width: Px, height: Px): SVG =
    val Visualization.Seq(a, b) = seq
    Length.divideProportionally(height.pixels)(a.length, b.length) match
      case IntegralProportions(k, sizes) =>
        val List(ha, hb) = sizes
        val g = SVG.Group(
          renderSVG(a, width * k, Px(ha)),
          renderSVG(b, width * k, Px(hb)).translate(0.0, ha),
        )
        if (k == 1) then g else g.scale(k)
  end renderSeq

  private def renderPar(par: Visualization.Par, width: Px, height: Px): SVG =
    val Visualization.Par(a, b) = par
    Breadth.divideProportionally(width.pixels)(a.breadth, b.breadth) match
      case IntegralProportions(k, sizes) =>
        val List(wa, wb) = sizes
        val g = SVG.Group(
          renderSVG(a, Px(wa), height * k),
          renderSVG(b, Px(wb), height * k).translate(wa, 0.0),
        )
        if (k == 1) then g else g.scale(k)
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