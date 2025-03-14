package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, SingletonValue, TypeEq}
import libretto.lambda.util.TypeEq.Refl
import scala.annotation.targetName

/** A collection of arrows `Ai -> B`,
 * where `As = name1 :: A1 || name2 :: A2 || ... || name_n :: An`,
 * where `||` associates to the left.
 */
opaque type SinkNAryNamed[->[_, _], ||[_, _], ::[_, _], As, B] =
  Items1Named.Product[||, ::, [Ai] =>> Ai -> B, As]

object SinkNAryNamed {

  def single[->[_, _], ||[_, _], ::[_, _], Lbl <: String, A, B](
    label: SingletonValue[Lbl],
    h: A -> B,
  ): SinkNAryNamed[->, ||, ::, Lbl :: A, B] =
    Items1Named.Product.single(label, h)

  def single[->[_, _], ||[_, _], ::[_, _], A, B](
    label: String,
  )(
    h: A -> B,
  ): SinkNAryNamed[->, ||, ::, label.type :: A, B] =
    Items1Named.Product.single(label)(h)

  def snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl <: String, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    lastLabel: SingletonValue[Lbl],
    last: Z -> R,
  ): SinkNAryNamed[->, ||, ::, Init || Lbl :: Z, R] =
    Items1Named.Product.Snoc(init, lastLabel, last)

  def snoc[->[_, _], ||[_, _], ::[_, _], Init, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    lastLabel: String,
    last: Z -> R,
  ): SinkNAryNamed[->, ||, ::, Init || lastLabel.type :: Z, R] =
    Items1Named.Product.Snoc(init, SingletonValue(lastLabel), last)

  def snoc[->[_, _], ||[_, _], ::[_, _], Init, Lbl <: String, Z, R](
    init: SinkNAryNamed[->, ||, ::, Init, R],
    lastLabel: SingletonValue[Lbl],
    last: SinkNAryNamed[->, ||, ::, Lbl :: Z, R]
  )(using
    BiInjective[::],
  ): SinkNAryNamed[->, ||, ::, Init || Lbl :: Z, R] =
    snoc(init, lastLabel, last.asSingle)

  extension [->[_, _], ||[_, _], ::[_, _], As, B](s: SinkNAryNamed[->, ||, ::, As, B]) {
    def get[LblX, X](m: Items1Named.Member[||, ::, LblX, X, As])(using
      BiInjective[||],
      BiInjective[::],
    ): X -> B =
      s.get(m)

    @targetName("snocExt")
    def snoc[Lbl <: String, Z](
      label: SingletonValue[Lbl],
      last: Z -> B,
    ): SinkNAryNamed[->, ||, ::, As || (Lbl :: Z), B] =
      SinkNAryNamed.snoc(s, label, last)

    @targetName("snocExt")
    def snoc[Z](
      label: String,
    )(
      last: Z -> B,
    ): SinkNAryNamed[->, ||, ::, As || (label.type :: Z), B] =
      SinkNAryNamed.snoc(s, label, last)

    def dropNames[∙[_, _], Nil]: Exists[[As0] =>> (
      DropNames[||, ::, ∙, Nil, As, As0],
      SinkNAry[->, ∙, Nil, As0, B]
    )] =
      s.dropNames[∙, Nil] match
        case Exists.Some((d, p)) =>
          Exists((d, SinkNAry.fromProduct(p)))

    def foldMap[->>[_, _]](
      baseCase: [Lbl <: String, A] => (SingletonValue[Lbl], A -> B) => (Lbl :: A) ->> B,
      snocCase: [Init, Lbl <: String, A] => (Init ->> B, SingletonValue[Lbl], A -> B) => (Init || Lbl :: A) ->> B,
    ): As ->> B =
      s.foldMap[[X] =>> X ->> B](baseCase, snocCase)

    def foldSemigroup[S](
      f: [x, y] => (x -> y) => S,
      g: (S, S) => S,
    ): S =
      s.foldMap[[X] =>> S](
        [Lbl <: String, A] => (_, h) => f(h),
        [Init, Lbl <: String, A] => (s, _, h) => g(s, f(h))
      )

    def translate[->>[_, _]](h: [x, y] => (x -> y) => (x ->> y)): SinkNAryNamed[->>, ||, ::, As, B] =
      s.translate[[X] =>> X ->> B]([x] => fxb => h(fxb))

    def translateA[G[_], ->>[_, _]](
      h: [x, y] => (x -> y) => G[x ->> y],
    )(using
      Applicative[G],
    ): G[SinkNAryNamed[->>, ||, ::, As, B]] =
      s.translateA[G, [X] =>> X ->> B]([x] => fxb => h(fxb))

    def forall(f: [x, y] => (x -> y) => Boolean): Boolean =
      s.forall([x] => fxb => f(fxb))
  }
}
