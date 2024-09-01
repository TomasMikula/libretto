package libretto.lambda.examples.workflow.generic.vis

trait Visualizable[F[_, _]] {
  extension [A, B](f: F[A, B])
    def visualize: Visualization
}
