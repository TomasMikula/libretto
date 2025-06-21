package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed

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

  def labeledBoxes[F[_, _], approximates[_, _]](
    inDesc: [A, B] => (A `approximates` B) => EdgeDesc[A],
    describe: [A, B] => F[A, B] => (
      String, // label
      Exists[approximates[_, A]],
      Exists[approximates[_, B]],
      Color
    ),
  ): Visualizer[F, approximates] =
    new Visualizer[F, approximates] {

      extension [A, B](f: F[A, B])
        override def visualize: Exists[[X] =>> Exists[[Y] =>> (approximates[X, A], approximates[Y, B], Visualization[X, Y])]] =
          describe(f) match
            case (label, Indeed(apprA), Indeed(apprB), color) =>
              Exists(Exists((
                apprA,
                apprB,
                Visualization.LabeledBox(inDesc(apprA), inDesc(apprB), label, Some(color)),
              )))


    }
}
