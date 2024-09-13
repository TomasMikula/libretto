package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.vis.*

object RenderSVG {
  def main(args: Array[String]): Unit =
    val W = 640
    val H = 480
    val graphic = FlowVisualizer.visualize(backgroundCheck)
    val svg: SVG = VisualizationToSVG.renderSVGToFit(graphic, W, H)
    svg.writeTo("background-check.svg", W, H)
}
