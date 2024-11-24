package libretto.lambda

/** An n-ary tuple of arrows `Ai -> Bi`,
 *  where
 *    `A = Nil ∙ A1 ∙ ... ∙ An`,
 *    `B = Nil ∙ B1 ∙ ... ∙ Bn`,
 *  where `∙` associates to the left.
 *
 * An arrowized version of [[TupleN]].
 */
trait ParN[∙[_, _], Nil, ->[_, _], A, B] {
  def size: Int

  def inputProjection[F[_]](
    f: [X, Y] => (X -> Y) => F[X],
  ): TupleN[∙, Nil, F, A]

  def outputProjection[G[_]](
    g: [X, Y] => (X -> Y) => G[Y],
  ): TupleN[∙, Nil, G, B]

  def translate[->>[_, _]](
    f: [X, Y] => (X -> Y) => (X ->> Y),
  ): ParN[∙, Nil, ->>, A, B]

  def foldCrush[T](
    crush: [X, Y] => (X -> Y) => T,
    reduce: (T, T) => T,
  ): T

  def exists(pred: [X, Y] => (X -> Y) => Boolean): Boolean =
    foldCrush(pred, _ || _)

  def nonEmpty[R](
    f: [a1, a2, b1, b2] => (A =:= (a1 ∙ a2), B =:= (b1 ∙ b2)) ?=> R,
  ): R

  def nonEmptyIn(
    pairIsNotNil: [x, y] => (x ∙ y) =:= Nil => Nothing,
  ): (A =:= Nil) => Nothing

  def nonEmptyOut(
    pairIsNotNil: [x, y] => (x ∙ y) =:= Nil => Nothing,
  ): (B =:= Nil) => Nothing

  def ∙[C, D](f: C -> D): ParN[∙, Nil, ->, A ∙ C, B ∙ D] =
    ParN.Snoc(this, f)
}

object ParN {

  case class Single[∙[_, _], Nil, ->[_, _], A, B](
    value: A -> B,
  ) extends ParN[∙, Nil, ->, Nil ∙ A, Nil ∙ B] {

    override def size: Int = 1

    override def inputProjection[F[_]](f: [X, Y] => (X -> Y) => F[X]): TupleN[∙, Nil, F, Nil ∙ A] =
      TupleN.Single(f(value))

    override def outputProjection[G[_]](g: [X, Y] => (X -> Y) => G[Y]): TupleN[∙, Nil, G, Nil ∙ B] =
      TupleN.Single(g(value))

    override def translate[->>[_,_]](f: [X, Y] => (X -> Y) => (X ->> Y)): ParN[∙, Nil, ->>, Nil ∙ A, Nil ∙ B] =
      Single(f(value))

    override def foldCrush[T](crush: [X, Y] => (X -> Y) => T, reduce: (T, T) => T): T =
      crush(value)

    override def nonEmpty[R](
      f: [a1, a2, b1, b2] => (Nil ∙ A =:= a1 ∙ a2, Nil ∙ B =:= b1 ∙ b2) ?=> R): R =
        f[Nil, A, Nil, B]

    override def nonEmptyIn(
      pairIsNotNil: [x, y] => (x ∙ y) =:= Nil => Nothing
    ): (Nil ∙ A) =:= Nil => Nothing =
      pairIsNotNil[Nil, A]

    override def nonEmptyOut(
      pairIsNotNil: [x, y] => (x ∙ y) =:= Nil => Nothing
    ): (Nil ∙ B) =:= Nil => Nothing =
      pairIsNotNil[Nil, B]

  }

  case class Snoc[∙[_, _], Nil, ->[_, _], A1, A2, B1, B2](
    init: ParN[∙, Nil, ->, A1, B1],
    last: A2 -> B2,
  ) extends ParN[∙, Nil, ->, A1 ∙ A2, B1 ∙ B2] {

    override def size: Int = 1 + init.size

    override def inputProjection[F[_]](f: [X, Y] => (X -> Y) => F[X]): TupleN[∙, Nil, F, A1 ∙ A2] =
      TupleN.Snoc(init.inputProjection(f), f(last))

    override def outputProjection[G[_]](g: [X, Y] => (X -> Y) => G[Y]): TupleN[∙, Nil, G, B1 ∙ B2] =
      TupleN.Snoc(init.outputProjection(g), g(last))

    override def translate[->>[_, _]](f: [X, Y] => (X -> Y) => (X ->> Y)): ParN[∙, Nil, ->>, A1 ∙ A2, B1 ∙ B2] =
      Snoc(init.translate(f), f(last))

    override def foldCrush[T](crush: [X, Y] => (X -> Y) => T, reduce: (T, T) => T): T =
      reduce(init.foldCrush(crush, reduce), crush(last))

    override def nonEmpty[R](
      f: [a1, a2, b1, b2] => (A1 ∙ A2 =:= a1 ∙ a2, B1 ∙ B2 =:= b1 ∙ b2) ?=> R,
    ): R =
      f[A1, A2, B1, B2]

    override def nonEmptyIn(
      pairIsNotNil: [x, y] => (x ∙ y) =:= Nil => Nothing
    ): (A1 ∙ A2) =:= Nil => Nothing =
      pairIsNotNil[A1, A2]

    override def nonEmptyOut(
      pairIsNotNil: [x, y] => (x ∙ y) =:= Nil => Nothing
    ): (B1 ∙ B2) =:= Nil => Nothing =
      pairIsNotNil[B1, B2]

  }

}
