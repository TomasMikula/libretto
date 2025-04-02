package libretto.lambda

import libretto.lambda.util.{Exists, SingletonType}

/** An n-ary tuple of arrows `Ai -> Bi`,
 *  such that
 *    `A = Nil ∙ A1 ∙ ... ∙ An`,
 *    `B = Nil ∙ B1 ∙ ... ∙ Bn`,
 *  where `∙` associates to the left.
 *
 * An arrowized version of [[Items1.Product]].
 */
sealed trait ParN[∙[_, _], Nil, ->[_, _], A, B] {
  def size: Int

  def inputProjection[F[_]](
    f: [X, Y] => (X -> Y) => F[X],
  ): TupleN[∙, Nil, F, A]

  def outputProjection[G[_]](
    g: [X, Y] => (X -> Y) => G[Y],
  ): TupleN[∙, Nil, G, B]

  def divide[F[_, _], G[_, _]](
    h: [X, Y] => (X -> Y) => Exists[[Q] =>> (F[X, Q], G[Q, Y])],
  ): Exists[[Q] =>> (
    ParN[∙, Nil, F, A, Q],
    ParN[∙, Nil, G, Q, B]
  )]

  def divide3[F[_, _], G[_, _], H[_, _]](
    h: [X, Y] => (X -> Y) => Exists[[P] =>> Exists[[Q] =>> (F[X, P], G[P, Q], H[Q, Y])]]
  ): Exists[[P] =>> Exists[[Q] =>> (
    ParN[∙, Nil, F, A, P],
    ParN[∙, Nil, G, P, Q],
    ParN[∙, Nil, H, Q, B],
  )]] = {
    type GH[P, Y] = Exists[[Q] =>> (G[P, Q], H[Q, Y])]
    divide[F, GH](
      [X, Y] => (f: X -> Y) => h(f) match {
        case Exists.Some(Exists.Some((f, g, h))) =>
          Exists((f, Exists((g, h))))
      }
    ) match {
      case Exists.Some((fs, ghs)) =>
        ghs.divide[G, H](
          [P, Y] => (gh: GH[P, Y]) => gh
        ) match {
          case Exists.Some((gs, hs)) =>
            Exists(Exists((fs, gs, hs)))
        }
    }

  }

  def flip: ParN[∙, Nil, [x, y] =>> y -> x, B, A]

  def translate[->>[_, _]](
    f: [X, Y] => (X -> Y) => (X ->> Y),
  ): ParN[∙, Nil, ->>, A, B]

  def foldL[G[_, _]](
    first: [x, y] => (x -> y) => G[Nil ∙ x, Nil ∙ y],
    snoc: [x1, x2, y1, y2] => (G[x1, y1], x2 -> y2) => G[x1 ∙ x2, y1 ∙ y2],
  ): G[A, B]

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

  type ZippedWithIndex[X, Y] = (X -> Y, TupleElem[∙, Nil, X, A], TupleElem[∙, Nil, Y, B])

  def zipWithIndex: ParN[∙, Nil, ZippedWithIndex, A, B]

  def toList[T](f: [X, Y] => (X -> Y) => T): List[T] =
    toList(f, Nil)

  protected def toList[T](
    f: [X, Y] => (X -> Y) => T,
    acc: List[T],
  ): List[T]
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

    override def divide[F[_,_], G[_,_]](
      h: [X, Y] => (X -> Y) => Exists[[Q] =>> (F[X, Q], G[Q, Y])],
    ): Exists[[Q] =>> (
      ParN[∙, Nil, F, Nil ∙ A, Q],
      ParN[∙, Nil, G, Q, Nil ∙ B]
    )] =
      h(value) match
        case Exists.Some((f, g)) =>
          Exists((Single(f), Single(g)))

    override def flip: ParN[∙, Nil, [x, y] =>> y -> x, Nil ∙ B, Nil ∙ A] =
      Single(value)

    override def translate[->>[_,_]](f: [X, Y] => (X -> Y) => (X ->> Y)): ParN[∙, Nil, ->>, Nil ∙ A, Nil ∙ B] =
      Single(f(value))

    override def foldL[G[_,_]](
      first: [x, y] => (x -> y) => G[Nil ∙ x, Nil ∙ y],
      snoc: [x1, x2, y1, y2] => (G[x1, y1], x2 -> y2) => G[x1 ∙ x2, y1 ∙ y2],
    ): G[Nil ∙ A, Nil ∙ B] =
      first(value)

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

    override def zipWithIndex: ParN[∙, Nil, [x, y] =>> (x -> y, TupleElem[∙, Nil, x, Nil ∙ A], TupleElem[∙, Nil, y, Nil ∙ B]), Nil ∙ A, Nil ∙ B] =
      Single((value, TupleElem.single, TupleElem.single))

    override protected def toList[T](f: [X, Y] => (X -> Y) => T, acc: List[T]): List[T] =
      f(value) :: acc

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

    override def divide[F[_,_], G[_,_]](
      h: [X, Y] => (X -> Y) => Exists[[Q] =>> (F[X, Q], G[Q, Y])],
    ): Exists[[Q] =>> (
      ParN[∙, Nil, F, A1 ∙ A2, Q],
      ParN[∙, Nil, G, Q, B1 ∙ B2]
    )] =
      (init.divide(h), h(last)) match
        case (Exists.Some((fInit, gInit)), Exists.Some((f, g))) =>
          Exists((Snoc(fInit, f), Snoc(gInit, g)))

    override def flip: ParN[∙, Nil, [x, y] =>> y -> x, B1 ∙ B2, A1 ∙ A2] =
      Snoc(init.flip, last)

    override def translate[->>[_, _]](f: [X, Y] => (X -> Y) => (X ->> Y)): ParN[∙, Nil, ->>, A1 ∙ A2, B1 ∙ B2] =
      Snoc(init.translate(f), f(last))

    override def foldL[G[_,_]](
      first: [x, y] => (x -> y) => G[Nil ∙ x, Nil ∙ y],
      snoc: [x1, x2, y1, y2] => (G[x1, y1], x2 -> y2) => G[x1 ∙ x2, y1 ∙ y2],
    ): G[A1 ∙ A2, B1 ∙ B2] =
      snoc(init.foldL(first, snoc), last)

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

    override def zipWithIndex: ParN[∙, Nil, [x, y] =>> (x -> y, TupleElem[∙, Nil, x, A1 ∙ A2], TupleElem[∙, Nil, y, B1 ∙ B2]), A1 ∙ A2, B1 ∙ B2] =
      init
        .zipWithIndex
        .translate[ZippedWithIndex]([x, y] => f => (f._1, f._2.inInit[A2], f._3.inInit[B2]))
        ∙ (last, TupleElem.Last(), TupleElem.Last())

    override protected def toList[T](f: [X, Y] => (X -> Y) => T, acc: List[T]): List[T] =
      init.toList(f, f(last) :: acc)

  }

  /** An n-ary tuple of arrows `Ai -> Bi`,
   *  such that
   *    `A = "name1" :: A1 || ... || "nameN" :: An`,
   *    `B = "name1" :: B1 || ... || "nameN" :: Bn`,
   *  where `||` associates to the left.
   *
   * Note that names of members of `B` are the same as those of `A`.
   *
   * A named version of [[ParN]].
   */
  sealed trait Named[||[_, _], ::[_, _], ->[_, _], A, B] {
    def extend[Lbl <: String, X, Y](
      label: SingletonType[Lbl],
      f: X -> Y,
    ): ParN.Named[||, ::, ->, A || (Lbl :: X), B || (Lbl :: Y)] =
      ParN.Named.Snoc(this, label, f)

    def translate[->>[_, _]](
      f: [X, Y] => (X -> Y) => (X ->> Y),
    ): ParN.Named[||, ::, ->>, A, B]
  }

  object Named {
    case class Single[||[_, _], ::[_, _], ->[_, _], Lbl <: String, A, B](
      label: SingletonType[Lbl],
      value: A -> B,
    ) extends ParN.Named[||, ::, ->, Lbl :: A, Lbl :: B] {
      override def translate[->>[_, _]](
        f: [X, Y] => (X -> Y) => (X ->> Y),
      ): Named[||, ::, ->>, Lbl :: A, Lbl :: B] =
        Single(label, f(value))
    }

    case class Snoc[||[_, _], ::[_, _], ->[_, _], AInit, BInit, Lbl <: String, C, D](
      init: ParN.Named[||, ::, ->, AInit, BInit],
      label: SingletonType[Lbl],
      last: C -> D,
    ) extends ParN.Named[||, ::, ->, AInit || (Lbl :: C), BInit || (Lbl :: D)] {

      override def translate[->>[_, _]](
        f: [X, Y] => (X -> Y) => (X ->>Y),
      ): Named[||, ::, ->>, AInit || Lbl :: C, BInit || Lbl :: D] =
        Snoc(init.translate(f), label, f(last))
    }
  }

}
