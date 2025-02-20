package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, TypeEq}
import libretto.lambda.util.TypeEq.Refl

/** A collection of arrows `Ai -> B`,
 * where `A = name1 :: A1 || name2 :: A2 || ... || name_n :: An`,
 * where `||` associates to the left.
 */
sealed trait SinkNAryNamed[->[_, _], ||[_, _], ::[_, _], A, B] {
  def translate[->>[_, _]](f: [x, y] => (x -> y) => (x ->> y)): SinkNAryNamed[->>, ||, ::, A, B]
  def translateA[->>[_, _], G[_]](f: [x, y] => (x -> y) => G[x ->> y])(using Applicative[G]): G[SinkNAryNamed[->>, ||, ::, A, B]]
  def foldSemigroup[S](
    f: [x, y] => (x -> y) => S,
    g: (S, S) => S,
  ): S
  def asSingle[LblX, X](using A =:= (LblX :: X), BiInjective[::]): X -> B

  def get[LblX, X](m: Member[||, ::, LblX, X, A])(using
    BiInjective[||],
    BiInjective[::],
  ): X -> B

  def dropNames[∙[_, _], Nil]: Exists[[A0] =>> (
    DropNames[||, ::, ∙, Nil, A, A0],
    SinkNAry[->, ∙, Nil, A0, B]
  )]

  def snoc[Lbl <: String, Z](
    label: Lbl,
    last: Z -> B,
  ): SinkNAryNamed[->, ||, ::, A || (Lbl :: Z), B] =
    SinkNAryNamed.Snoc(this, label, last)

  def forall(f: [x, y] => (x -> y) => Boolean): Boolean =
    foldSemigroup[Boolean](f, _ && _)
}

object SinkNAryNamed {
  case class Single[->[_, _], ||[_, _], ::[_, _], Lbl <: String, A, B](
    label: Lbl,
    h: A -> B,
  ) extends SinkNAryNamed[->, ||, ::, Lbl :: A, B] {
    override def translate[->>[_, _]](
      f: [x, y] => (x -> y) => (x ->> y),
    ): SinkNAryNamed[->>, ||, ::, Lbl :: A, B] =
      Single(label, f(h))

    override def translateA[->>[_, _], G[_]](
      f: [x, y] => (x -> y) => G[x ->> y],
    )(using
      Applicative[G],
    ): G[SinkNAryNamed[->>, ||, ::, Lbl :: A, B]] =
      f(h).map(Single(label, _))

    override def foldSemigroup[S](f: [x, y] => (x -> y) => S, g: (S, S) => S): S =
      f(h)

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

    override def dropNames[∙[_,_], Nil]: Exists[[A0] =>> (
      DropNames[||, ::, ∙, Nil, Lbl :: A, A0],
      SinkNAry[->, ∙, Nil, A0, B]
    )] =
      Exists((
        DropNames.Single(),
        SinkNAry.Single(h)
      ))
  }

  case class Snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl <: String, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    label: Lbl,
    last: Z -> R,
  ) extends SinkNAryNamed[->, ||, ::, Init || (Lbl :: Z), R] {
    override def translate[->>[_, _]](
      f: [x, y] => (x -> y) => (x ->> y),
    ): SinkNAryNamed[->>, ||, ::, Init || Lbl :: Z, R] =
      Snoc(
        init.translate(f),
        label,
        f(last),
      )

    override def translateA[->>[_, _], G[_]](
      f: [x, y] => (x -> y) => G[x ->> y],
    )(using
      G: Applicative[G],
    ): G[SinkNAryNamed[->>, ||, ::, Init || Lbl :: Z, R]] =
      G.map2(init.translateA(f), f(last)) { Snoc(_, label, _) }

    override def foldSemigroup[S](f: [x, y] => (x -> y) => S, g: (S, S) => S): S =
      g(init.foldSemigroup(f, g), f(last))

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

    override def dropNames[∙[_,_], Nil]: Exists[[A0] =>> (
      DropNames[||, ::, ∙, Nil, Init || Lbl :: Z, A0],
      SinkNAry[->, ∙, Nil, A0, R]
    )] =
      init.dropNames[∙, Nil] match
        case Exists.Some((drop0, sink0)) =>
          Exists((drop0.inInit[Lbl, Z], SinkNAry.Snoc(sink0, last)))
  }

  def snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl <: String, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    lastLabel: Lbl,
    last: SinkNAryNamed[->, ||, ::, Lbl :: Z, R]
  )(using
    BiInjective[::],
  ): SinkNAryNamed[->, ||, ::, Init || Lbl :: Z, R] =
    Snoc(init, lastLabel, last.asSingle)
}
