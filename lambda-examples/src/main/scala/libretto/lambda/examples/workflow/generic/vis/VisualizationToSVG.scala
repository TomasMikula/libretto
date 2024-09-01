package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.examples.workflow.generic.vis.SVG.FontFamily.Monospace
import libretto.lambda.examples.workflow.generic.vis.SVG.*
import libretto.lambda.examples.workflow.generic.vis.Visualization.Unimplemented

object VisualizationToSVG {
  /** Render to a 1024x1024 bounding rectangle (not including ports). */
  def renderSVG(g: Visualization): SVG =
    val r = g.heightToWidthRatio
    val (w, h) =
      if r > 1.0
      then (1024/r, 1024.0)
      else (1024.0, 1024*r)

    renderSVG(g, w, h)

  def renderSVG(g: Visualization, width: Double, height: Double): SVG =
    g match
      case Unimplemented(label) =>
        val text = SVG.Text(label, x = 0.px, y = 20.px, Monospace, fontSize = 20.px)
        val th = text.fontSize
        val tw = label.length * th.pixels * 0.6 // XXX
        val scale = scaleToFit(tw, th.pixels, width, height)
        SVG.Transformed(text, SVG.Transform.Scale(scale))

  private def scaleToFit(srcW: Double, srcH: Double, tgtW: Double, tgtH: Double): Double =
    val scaleW = tgtW / srcW
    val scaleH = tgtH / srcH
    math.min(scaleW, scaleH)
}