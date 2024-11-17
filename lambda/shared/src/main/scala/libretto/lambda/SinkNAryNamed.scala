package libretto.lambda

import libretto.lambda.util.{BiInjective, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** A collection of arrows `Ai --> B`,
 * where `A = name1 :: A1 || name2 :: A2 || ... || name_n :: An`,
 * where `||` associates to the left.
 */
sealed trait SinkNAryNamed[->[_, _], ||[_, _], ::[_, _], A, B] {
  def translate[->>[_, _]](f: [x, y] => (x -> y) => (x ->> y)): SinkNAryNamed[->>, ||, ::, A, B]
  def asSingle[LblX, X](using A =:= (LblX :: X), BiInjective[::]): X -> B

  def get[LblX, X](m: Member[||, ::, LblX, X, A])(using
    BiInjective[||],
    BiInjective[::],
  ): X -> B
}

private object SinkNAryNamed {
  case class Single[->[_, _], ||[_, _], ::[_, _], Lbl, A, B](
    h: A -> B,
  ) extends SinkNAryNamed[->, ||, ::, Lbl :: A, B] {
    override def translate[->>[_, _]](
      f: [x, y] => (x -> y) => (x ->> y),
    ): SinkNAryNamed[->>, ||, ::, Lbl :: A, B] =
      Single(f(h))

    override def asSingle[LblX, X](using
      ev: Lbl :: A =:= LblX :: X,
      i: BiInjective[::],
    ): X -> B =
      ev match { case BiInjective[::](_, TypeEq(Refl())) =>
        h
      }

    override def get[LblX, X](m: Member[||, ::, LblX, X, Lbl :: A])(using BiInjective[||], BiInjective[::]): X -> B =
      Member.asSingle(m) match
        case (lbl, TypeEq(Refl()), TypeEq(Refl())) =>
          h
  }

  case class Snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    last: Z -> R,
  ) extends SinkNAryNamed[->, ||, ::, Init || (Lbl :: Z), R] {
    override def translate[->>[_, _]](
      f: [x, y] => (x -> y) => (x ->> y),
    ): SinkNAryNamed[->>, ||, ::, Init || Lbl :: Z, R] =
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

    override def get[LblX, X](
      m: Member[||, ::, LblX, X, Init || Lbl :: Z],
    )(using
      BiInjective[||],
      BiInjective[::],
    ): X -> R =
      Member.asMultiple(m) match
        case Left((lbl, TypeEq(Refl()), TypeEq(Refl()))) => last
        case Right(m1) => init.get(m1)
  }

  def snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    last: SinkNAryNamed[->, ||, ::, Lbl :: Z, R]
  )(using
    BiInjective[::],
  ): SinkNAryNamed[->, ||, ::, Init || Lbl :: Z, R] =
    Snoc(init, last.asSingle)
}
