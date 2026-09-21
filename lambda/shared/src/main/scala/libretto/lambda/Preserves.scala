package libretto.lambda

infix trait Preserves2[Rel[_, _, _], Prop[_]] {
  def apply[A: Prop, B: Prop, C](rel: Rel[A, B, C]): Prop[C]
}
