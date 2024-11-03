package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.vis.*
import libretto.lambda.util.Exists.{Some as ∃}
import libretto.lambda.examples.workflow.subdomains.equipmentRequest.equipmentRequest

object RenderSVG {
  def main(args: Array[String]): Unit =
    val W = 800
    val H = 800
    FlowVisualizer[Activity].visualize(equipmentRequest.shakeUp) match
      case ∃(∃((_, _, graphic))) =>
        VisualizationToSVG
          .renderSVGToFit(graphic, W, H)
          .writeTo("equipment-request.svg", W, H)
}
