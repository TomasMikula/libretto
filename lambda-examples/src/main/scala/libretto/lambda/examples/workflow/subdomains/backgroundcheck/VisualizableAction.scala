package libretto.lambda.examples.workflow.subdomains.backgroundcheck

import libretto.lambda.examples.workflow.generic.vis.{Visualizable, Visualization}

given Visualizable[Action] with {
  extension [A, B](f: Action[A, B])
    override def visualize: Visualization =
      Visualization.Unimplemented(f.getClass.getSimpleName)
}
