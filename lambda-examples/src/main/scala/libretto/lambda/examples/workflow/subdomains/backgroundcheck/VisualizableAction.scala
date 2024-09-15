package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.vis.{Approximates, Visualization, Visualizer}
import libretto.lambda.util.Exists

given Visualizer[Action, Approximates] with {
  extension [A, B](f: Action[A, B])
    override def visualize: Exists[[X] =>> Exists[[Y] =>> (
      X Approximates A,
      Y Approximates B,
      Visualization[X, Y],
    )]] =
      val label =
        Option(f.getClass.getSimpleName)
          .filter(_.nonEmpty)
          .orElse(Option(f.toString))
          .filter(_.nonEmpty)
          .getOrElse("<unnamed>")
      Visualizer.unimplemented(label)
}
