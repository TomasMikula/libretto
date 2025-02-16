package libretto.lambda.examples.workflow.subdomains.equipmentRequest

import libretto.lambda.examples.workflow.generic.lang.*
import libretto.lambda.examples.workflow.generic.runtime.Value
import libretto.lambda.examples.workflow.generic.runtime.PortId
import libretto.lambda.util.Exists
import libretto.lambda.examples.workflow.generic.runtime.Value.Inject

sealed trait Val[A] {
  def uninhabited: Nothing
}

object Val {
  given Value.Compliant[Val] with {
    override def extractString(value: Val[Str]): String = value.uninhabited
    override def unzip[A, B](fab: Val[A ** B]): (Val[A], Val[B]) = fab.uninhabited
    override def toEither[A, B](value: Val[A ++ B]): Either[Val[A], Val[B]] = value.uninhabited
    override def extractPortId[A](value: Val[Reading[A]]): PortId[A] = value.uninhabited
    override def revealCase[Cases](value: Val[Enum[Cases]]): Exists[[Lbl] =>> Exists[[A] =>> Inject[Val, Lbl, A, Cases]]] = value.uninhabited
  }
}
