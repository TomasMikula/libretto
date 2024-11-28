package libretto.lambda.examples.workflow.generic.vis

import libretto.lambda.TupleElem

sealed trait EdgeSegment[X, Y] {
  import EdgeSegment.*

  def inl[∙[_, _], B]: EdgeSegment[X, Y ∙ B] = Inl(this)
  def inr[∙[_, _], A]: EdgeSegment[X, A ∙ Y] = Inr(this)

  infix def compose[W](that: EdgeSegment[W, X]): EdgeSegment[W, Y]

  def switch[R](
    caseId: (X =:= Y) ?=> R,
    caseInl: [∙[_, _], Y1, Q] => (Y =:= (Y1 ∙ Q)) ?=> EdgeSegment[X, Y1] => R,
    caseInr: [∙[_, _], Y2, P] => (Y =:= (P ∙ Y2)) ?=> EdgeSegment[X, Y2] => R,
    caseElem: [Wrap[_], T, Ts] => (Y =:= Wrap[Ts]) ?=> (EdgeSegment[X, T], TupleElem[Tuple2, EmptyTuple, T, Ts]) => R,
  ): R
}

object EdgeSegment {
  case class Id[A]() extends EdgeSegment[A, A] {
    override def switch[R](
      caseId: (A =:= A) ?=> R,
      caseInl: [∘[_, _], Y1, Q] => (A =:= (Y1 ∘ Q)) ?=> EdgeSegment[A, Y1] => R,
      caseSnd: [∘[_, _], Y2, P] => (A =:= (P ∘ Y2)) ?=> EdgeSegment[A, Y2] => R,
      caseElem: [Wrap[_], T, Ts] => (A =:= Wrap[Ts]) ?=> (EdgeSegment[A, T], TupleElem[Tuple2, EmptyTuple, T, Ts]) => R,
    ): R =
      caseId

    override def compose[W](that: EdgeSegment[W, A]): EdgeSegment[W, A] =
      that
  }

  sealed trait Sub[X, Y] extends EdgeSegment[X, Y]

  case class Inl[∙[_, _], A, B, Q](l: EdgeSegment[A, B]) extends EdgeSegment.Sub[A, B ∙ Q] {
    override def switch[R](
      caseId: (A =:= (B ∙ Q)) ?=> R,
      caseInl: [∘[_, _], Y1, V] => ((B ∙ Q) =:= (Y1 ∘ V)) ?=> EdgeSegment[A, Y1] => R,
      caseInr: [∘[_, _], Y2, U] => ((B ∙ Q) =:= (U ∘ Y2)) ?=> EdgeSegment[A, Y2] => R,
      caseElem: [Wrap[_], T, Ts] => ((B ∙ Q) =:= Wrap[Ts]) ?=> (EdgeSegment[A, T], TupleElem[Tuple2, EmptyTuple, T, Ts]) => R,
    ): R =
      caseInl[∙, B, Q](l)

    override def compose[W](that: EdgeSegment[W, A]): EdgeSegment[W, B ∙ Q] =
      Inl(l.compose(that))
  }

  case class Inr[∙[_, _], A, B, P](r: EdgeSegment[A, B]) extends EdgeSegment.Sub[A, P ∙ B] {
    override def switch[R](
      caseId: (A =:= (P ∙ B)) ?=> R,
      caseInl: [∘[_, _], Y1, V] => ((P ∙ B) =:= (Y1 ∘ V)) ?=> EdgeSegment[A, Y1] => R,
      caseInr: [∘[_, _], Y2, U] => ((P ∙ B) =:= (U ∘ Y2)) ?=> EdgeSegment[A, Y2] => R,
      caseElem: [Wrap[_], T, Ts] => ((P ∙ B) =:= Wrap[Ts]) ?=> (EdgeSegment[A, T], TupleElem[Tuple2, EmptyTuple, T, Ts]) => R,
    ): R =
      caseInr[∙, B, P](r)

    override def compose[W](that: EdgeSegment[W, A]): EdgeSegment[W, P ∙ B] =
      Inr(r.compose(that))
  }

  case class InElem[Wrap[_], A, B, Bs](
    nested: EdgeSegment[A, B],
    elem: TupleElem[Tuple2, EmptyTuple, B, Bs],
  ) extends EdgeSegment.Sub[A, Wrap[Bs]] {
    override def switch[R](
      caseId: (A =:= Wrap[Bs]) ?=> R,
      caseInl: [∙[_,_], Y1, Q] => (Wrap[Bs] =:= ∙[Y1, Q]) ?=> EdgeSegment[A, Y1] => R,
      caseInr: [∙[_,_], Y2, P] => (Wrap[Bs] =:= ∙[P, Y2]) ?=> EdgeSegment[A, Y2] => R,
      caseElem: [Wr[_], T, Ts] => (Wrap[Bs] =:= Wr[Ts]) ?=> (EdgeSegment[A, T], TupleElem[Tuple2, EmptyTuple, T, Ts]) => R,
    ): R =
      caseElem[Wrap, B, Bs](nested, elem)

    override def compose[W](that: EdgeSegment[W, A]): EdgeSegment[W, Wrap[Bs]] =
      InElem(nested.compose(that), elem)

    def inInit[C]: InElem[Wrap, A, B, (Bs, C)] =
      InElem(nested, elem.inInit[C])
  }

  def pickId[A]: EdgeSegment[A, A] = Id()
  def pickL[∙[_, _], A, B]: EdgeSegment[A, A ∙ B] = Inl(Id[A]())
  def pickR[∙[_, _], A, B]: EdgeSegment[B, A ∙ B] = Inr(Id[B]())
  def elem[Wrap[_], A, As](el: TupleElem[Tuple2, EmptyTuple, A, As]): InElem[Wrap, A, A, As] = InElem(Id(), el)
}
