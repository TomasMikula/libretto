package libretto.lambda.examples.workflow.generic.vis

type WirePick[X] = EdgeSegment[Wire, X]

object WirePick {
  def pickId: WirePick[Wire] = EdgeSegment.pickId
  def pickL[∙[_, _], B]: WirePick[Wire ∙ B] = EdgeSegment.pickL
  def pickR[∙[_, _], A]: WirePick[A ∙ Wire] = EdgeSegment.pickR
}
