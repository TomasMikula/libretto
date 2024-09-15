package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.vis.*
import libretto.lambda.util.Exists.{Some as ∃}

object RenderSVG {
  def main(args: Array[String]): Unit =
    val W = 800
    val H = 800
    FlowVisualizer[Action].visualize(backgroundCheck) match
      case ∃(∃((_, _, graphic))) =>
        VisualizationToSVG
          .renderSVGToFit(graphic, W, H)
          .writeTo("background-check.svg", W, H)
}
