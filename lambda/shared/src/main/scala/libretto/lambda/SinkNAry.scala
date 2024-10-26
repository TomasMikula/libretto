package libretto.lambda

import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** A collection of arrows `Ai --> B`,
 * where `A = name1 :: A1 || name2 :: A2 || ... || name_n :: An`,
 * where `||` assiciates to the left.
 */
sealed trait SinkNAry[->[_, _], ||[_, _], ::[_, _], A, B] {
  def translate[->>[_, _]](f: [x, y] => (x -> y) => (x ->> y)): SinkNAry[->>, ||, ::, A, B]
  def asSingle[LblX, X](using A =:= (LblX :: X), BiInjective[::]): X -> B
}

private object SinkNAry {
  case class Single[->[_, _], ||[_, _], ::[_, _], Lbl, A, B](
    h: A -> B,
  ) extends SinkNAry[->, ||, ::, Lbl :: A, B] {
    override def translate[->>[_, _]](
      f: [x, y] => (x -> y) => (x ->> y),
    ): SinkNAry[->>, ||, ::, Lbl :: A, B] =
      Single(f(h))

    override def asSingle[LblX, X](using
      ev: Lbl :: A =:= LblX :: X,
      i: BiInjective[::],
    ): X -> B =
      ev match { case BiInjective[::](_, TypeEq(Refl())) =>
        h
      }
  }

  case class Snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl, Z, R](
    init: SinkNAry[->, ||, ::, Init, R],
    last: Z -> R,
  ) extends SinkNAry[->, ||, ::, Init || (Lbl :: Z), R] {
    override def translate[->>[_, _]](
      f: [x, y] => (x -> y) => (x ->> y),
    ): SinkNAry[->>, ||, ::, Init || Lbl :: Z, R] =
      Snoc(
        init.translate(f),
        f(last),
      )

    override def asSingle[LblX, X](using
      (Init || (Lbl :: Z)) =:= LblX :: X,
      BiInjective[::],
    ): X -> R =
      // TODO: require evidence that `||` and `::` cannot possibly be equal.
      throw AssertionError(s"Impossible (A || B) =:= (C :: D), assuming || and :: are distinct class types (are they?).")
  }

  def snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl, Z, R](
    init: SinkNAry[->, ||, ::, Init, R],
    last: SinkNAry[->, ||, ::, Lbl :: Z, R]
  )(using
    BiInjective[::],
  ): SinkNAry[->, ||, ::, Init || Lbl :: Z, R] =
    Snoc(init, last.asSingle)
}
