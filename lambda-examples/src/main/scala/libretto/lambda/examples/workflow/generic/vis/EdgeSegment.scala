package libretto.lambda.examples.workflow.generic.vis

sealed trait EdgeSegment[X, Y] {
  import EdgeSegment.*

  def inl[∙[_, _], B]: EdgeSegment[X, Y ∙ B] = Inl(this)
  def inr[∙[_, _], A]: EdgeSegment[X, A ∙ Y] = Inr(this)

  def switch[R](
    caseId: (X =:= Y) ?=> R,
    caseInl: [∙[_, _], Y1, Q] => (Y =:= (Y1 ∙ Q)) ?=> EdgeSegment[X, Y1] => R,
    caseInr: [∙[_, _], Y2, P] => (Y =:= (P ∙ Y2)) ?=> EdgeSegment[X, Y2] => R,
  ): R
}

object EdgeSegment {
  case class Id[A]() extends EdgeSegment[A, A] {
    override def switch[R](
      caseId: (A =:= A) ?=> R,
      caseInl: [∘[_, _], Y1, Q] => (A =:= (Y1 ∘ Q)) ?=> EdgeSegment[A, Y1] => R,
      caseSnd: [∘[_, _], Y2, P] => (A =:= (P ∘ Y2)) ?=> EdgeSegment[A, Y2] => R,
    ): R =
      caseId
  }

  sealed trait Sub[X, Y] extends EdgeSegment[X, Y]

  case class Inl[∙[_, _], A, B, Q](l: EdgeSegment[A, B]) extends EdgeSegment.Sub[A, B ∙ Q] {
    override def switch[R](
      caseId: (A =:= (B ∙ Q)) ?=> R,
      caseInl: [∘[_, _], Y1, V] => ((B ∙ Q) =:= (Y1 ∘ V)) ?=> EdgeSegment[A, Y1] => R,
      caseInr: [∘[_, _], Y2, U] => ((B ∙ Q) =:= (U ∘ Y2)) ?=> EdgeSegment[A, Y2] => R,
    ): R =
      caseInl[∙, B, Q](l)
  }

  case class Inr[∙[_, _], A, B, P](r: EdgeSegment[A, B]) extends EdgeSegment.Sub[A, P ∙ B] {
    override def switch[R](
      caseId: (A =:= (P ∙ B)) ?=> R,
      caseInl: [∘[_, _], Y1, V] => ((P ∙ B) =:= (Y1 ∘ V)) ?=> EdgeSegment[A, Y1] => R,
      caseInr: [∘[_, _], Y2, U] => ((P ∙ B) =:= (U ∘ Y2)) ?=> EdgeSegment[A, Y2] => R,
    ): R =
      caseInr[∙, B, P](r)
  }

  def pickId[A]: EdgeSegment[A, A] = Id()
  def pickL[∙[_, _], A, B]: EdgeSegment[A, A ∙ B] = Inl(Id[A]())
  def pickR[∙[_, _], A, B]: EdgeSegment[B, A ∙ B] = Inr(Id[B]())
}
