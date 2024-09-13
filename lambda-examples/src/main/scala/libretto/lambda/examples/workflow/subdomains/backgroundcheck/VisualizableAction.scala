package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.vis.{Visualizable, Visualization}

given Visualizable[Action] with {
  extension [A, B](f: Action[A, B])
    override def visualize: Visualization =
      val label =
        Option(f.getClass.getSimpleName)
          .filter(_.nonEmpty)
          .orElse(Option(f.toString))
          .filter(_.nonEmpty)
          .getOrElse("<unnamed>")
      Visualization.Unimplemented(label)
}
