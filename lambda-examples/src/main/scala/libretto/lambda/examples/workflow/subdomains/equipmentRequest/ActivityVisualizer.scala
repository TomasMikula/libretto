package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.vis.{Approximates, Color, Visualization, Visualizer, Wire}
import libretto.lambda.examples.workflow.generic.vis.Approximates.lump
import libretto.lambda.util.Exists

given Visualizer[Activity, Approximates] = {
  val COLOR = Color.rgb(251, 159, 251)

  Visualizer.labeledBoxes(
    [A, B] => (appr: A Approximates B) =>
      appr.inDesc,
    [A, B] => (a: Activity[A, B]) => a match
        case Activity.RequestMonitorFromIT =>
          ("RequestMonitorFromIT", Exists(lump), Exists(lump), COLOR)
        case Activity.RequestChairFromOfficeMgmt =>
          ("RequestChairFromOfficeMgmt", Exists(lump), Exists(lump), COLOR)
        case Activity.OrderFromSupplier =>
          ("OrderFromSupplier", Exists(lump), Exists(lump), COLOR)
  )
}
