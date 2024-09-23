package libretto.lambda.examples.workflow.generic.vis

sealed trait WirePick[X] {
  import WirePick.*

  def inl[∙[_, _], B]: WirePick[X ∙ B] = Inl(this)
  def inr[∙[_, _], A]: WirePick[A ∙ X] = Inr(this)
  def inFst[B]: WirePick[(X, B)] = inl[Tuple2, B]
  def inSnd[A]: WirePick[(A, X)] = inr[Tuple2, A]

  def switch[R](
    caseId: (X =:= Wire) ?=> R,
    caseInl: [∙[_, _], X1, X2] => (X =:= (X1 ∙ X2)) ?=> WirePick[X1] => R,
    caseInr: [∙[_, _], X1, X2] => (X =:= (X1 ∙ X2)) ?=> WirePick[X2] => R,
  ): R
}

object WirePick {
  case object Id extends WirePick[Wire] {
    override def switch[R](
      caseId: (Wire =:= Wire) ?=> R,
      caseInl: [∘[_, _], X1, X2] => (Wire =:= (X1 ∘ X2)) ?=> WirePick[X1] => R,
      caseSnd: [∘[_, _], X1, X2] => (Wire =:= (X1 ∘ X2)) ?=> WirePick[X2] => R,
    ): R =
      caseId
  }

  case class Inl[∙[_, _], A, B](l: WirePick[A]) extends WirePick[A ∙ B] {
    override def switch[R](
      caseId: ((A ∙ B) =:= Wire) ?=> R,
      caseInl: [∘[_, _], X1, X2] => ((A ∙ B) =:= (X1 ∘ X2)) ?=> WirePick[X1] => R,
      caseInr: [∘[_, _], X1, X2] => ((A ∙ B) =:= (X1 ∘ X2)) ?=> WirePick[X2] => R,
    ): R =
      caseInl[∙, A, B](l)
  }

  case class Inr[∙[_, _], A, B](r: WirePick[B]) extends WirePick[A ∙ B] {
    override def switch[R](
      caseId: ((A ∙ B) =:= Wire) ?=> R,
      caseInl: [∘[_, _], X1, X2] => ((A ∙ B) =:= (X1 ∘ X2)) ?=> WirePick[X1] => R,
      caseInr: [∘[_, _], X1, X2] => ((A ∙ B) =:= (X1 ∘ X2)) ?=> WirePick[X2] => R,
    ): R =
      caseInr[∙, A, B](r)
  }

  def pickL[∙[_, _], B]: WirePick[Wire ∙ B] = Inl(Id)
  def pickR[∙[_, _], A]: WirePick[A ∙ Wire] = Inr(Id)
}
