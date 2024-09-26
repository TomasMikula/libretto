package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.util.Exists

trait Visualizer[F[_, _], approximates[_, _]] {
  extension [A, B](f: F[A, B])
    def visualize: Exists[[X] =>> Exists[[Y] =>> (
      X `approximates` A,
      Y `approximates` B,
      Visualization[X, Y]
    )]]
}

object Visualizer {
  def unimplemented[approximates[_, _], A, B](
    label: String,
  )(using
    appr: Approximation[approximates],
  ): Exists[[X] =>> Exists[[Y] =>> (
    X `approximates` A,
    Y `approximates` B,
    Visualization[X, Y]
  )]] =
    Exists(Exists((
      appr.lump[A],
      appr.lump[B],
      Visualization.Unimplemented(label, EdgeDesc.wire, EdgeDesc.wire),
    )))
}
