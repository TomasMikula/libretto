package libretto.lambda

infix trait Preserves[Rel[_, _], Prop[_]] {
  def apply[A: Prop, B](rel: Rel[A, B]): Prop[B]
}

infix trait Preserves2[Rel[_, _, _], Prop[_]] {
  def apply[A: Prop, B: Prop, C](rel: Rel[A, B, C]): Prop[C]
}
