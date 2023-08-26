package libretto.lambda.examples.workflow.generic.runtime

import libretto.lambda.Tupled
import libretto.lambda.examples.workflow.generic.lang.**


opaque type Cap[Val[_], A] = Tupled[**, Cap.Leaf[Val, _], A]

object Cap {
  enum Leaf[Val[_], A]:
    case Input(value: Value[Val, A])
    case Promised()

  def input[Val[_], A](value: Value[Val, A]): Cap[Val, A] =
    Tupled.atom(Leaf.Input(value))
}
