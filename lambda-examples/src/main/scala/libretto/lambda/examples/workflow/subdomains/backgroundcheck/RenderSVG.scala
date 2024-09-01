package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.vis.*

object RenderSVG {
  def main(args: Array[String]): Unit =
    val graphic = FlowVisualizer.visualize(backgroundCheck)
    val svg: SVG = VisualizationToSVG.renderSVG(graphic)
    svg.writeTo("background-check.svg")
}
