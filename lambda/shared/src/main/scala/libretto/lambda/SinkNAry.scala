package libretto.lambda

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed

/** A collection of arrows `Ai -> B`,
 * where `A = Nil || A1 || A2 || ... || An`,
 * where `||` associates to the left.
 */
trait SinkNAry[->[_, _], ||[_, _], Nil, A, B] {
  import SinkNAry.to

  def andThen[C](g: B -> C)(using Semigroupoid[->]): SinkNAry[->, ||, Nil, A, C]

  def changeTarget[C](f: [X] => (X -> B) => (X -> C)): SinkNAry[->, ||, Nil, A, C]

  def translate[->>[_, _]](f: [X, Y] => (X -> Y) => (X ->> Y)): SinkNAry[->>, ||, Nil, A, B]

  def asSource: SourceNAry[[x, y] =>> y -> x, ||, Nil, B, A]

  /** N-ary pullback from binary, generalized in that the arrows
   *  of the resulting source (n-ary span) may be of a different type `->>`.
   */
  def pullback[->>[_, _], Obj[_]](
    binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (Obj[P], P ->> X, P ->> Y, P -> Q)],
    srcData: [X, Y] => (X -> Y) => Obj[X],
  )(using
    NarrowCategory[Obj, ->>],
  ): Exists[[P] =>> (SourceNAry[->>, ||, Nil, P, A], P -> B)] =
    pullback_(binaryPullback, srcData) match
      case Indeed((_, source, p)) =>
        Indeed((source.translate[->>]([X, Y] => f => f._1), p))

  protected def pullback_[->>[_, _], Obj[_]](
    binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (Obj[P], P ->> X, P ->> Y, P -> Q)],
    srcData: [X, Y] => (X -> Y) => Obj[X],
  )(using
    NarrowCategory[Obj, ->>],
  ): Exists[[P] =>> (Obj[P], SourceNAry[->> to Obj, ||, Nil, P, A], P -> B)]

  def divide[F[_, _], G[_, _]](
    h: [X, Y] => (X -> Y) => Exists[[Q] =>> (F[X, Q], G[Q, Y])],
  ): Exists[[Q] =>> (
    ParN[||, Nil, F, A, Q],
    SinkNAry[G, ||, Nil, Q, B],
  )]

  def divide3[F[_, _], G[_, _], H[_, _]](
    h: [X, Y] => (X -> Y) => Exists[[P] =>> Exists[[Q] =>> (F[X, P], G[P, Q], H[Q, Y])]],
  ): Exists[[P] =>> Exists[[Q] =>> (
    ParN[||, Nil, F, A, P],
    ParN[||, Nil, G, P, Q],
    SinkNAry[H, ||, Nil, Q, B],
  )]]
}

object SinkNAry {
  private[SinkNAry] infix type to[->[_, _], Tgt[_]] = [A, B] =>> (A -> B, Tgt[B])

  case class Single[->[_, _], ||[_, _], Nil, A, B](
    f: A -> B,
  ) extends SinkNAry[->, ||, Nil, Nil || A, B] {

    override def andThen[C](g: B -> C)(using Semigroupoid[->]): SinkNAry[->, ||, Nil, Nil || A, C] =
      Single(f > g)

    override def changeTarget[C](g: [X] => (X -> B) => X -> C): SinkNAry[->, ||, Nil, Nil || A, C] =
      Single(g(f))

    override def translate[->>[_,_]](g: [X, Y] => (X -> Y) => (X ->> Y)): SinkNAry[->>, ||, Nil, Nil || A, B] =
      Single(g(f))

    override protected def pullback_[->>[_,_], Obj[_]](
      binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (Obj[P], P ->> X, P ->> Y, P -> Q)],
      srcData: [X, Y] => (X -> Y) => Obj[X],
    )(using
      cat: NarrowCategory[Obj, ->>],
    ): Exists[[P] =>> (Obj[P], SourceNAry[->> to Obj, ||, Nil, P, Nil || A], P -> B)] =
      given a: Obj[A] = srcData(f)
      Exists((
        a,
        SourceNAry.Single((cat.id[A], a)),
        f
      ))

    override def asSource: SourceNAry[[x, y] =>> y -> x, ||, Nil, B, Nil || A] =
      SourceNAry.Single(f)

    override def divide[F[_,_], G[_,_]](
      h: [X, Y] => (X -> Y) => Exists[[Q] =>> (F[X, Q], G[Q, Y])],
    ): Exists[[Q] =>> (
      ParN[||, Nil, F, Nil || A, Q],
      SinkNAry[G, ||, Nil, Q, B],
    )] =
      h(f) match
        case Indeed((f, g)) =>
          Exists((ParN.Single(f), SinkNAry.Single(g)))

    override def divide3[F[_,_], G[_,_], H[_,_]](
      h: [X, Y] => (X -> Y) => Exists[[P] =>> Exists[[Q] =>> (F[X, P], G[P, Q], H[Q, Y])]],
    ): Exists[[P] =>> Exists[[Q] =>> (
      ParN[||, Nil, F, Nil || A, P],
      ParN[||, Nil, G, P, Q],
      SinkNAry[H, ||, Nil, Q, B],
    )]] =
      h(f) match
        case Indeed(Indeed((f, g, h))) =>
          Exists(Exists((ParN.Single(f), ParN.Single(g), SinkNAry.Single(h))))
  }

  case class Snoc[->[_, _], ||[_, _], Nil, Init, Z, B](
    init: SinkNAry[->, ||, Nil, Init, B],
    last: Z -> B,
  ) extends SinkNAry[->, ||, Nil, Init || Z, B] {

    override def andThen[C](g: B -> C)(using Semigroupoid[->]): SinkNAry[->, ||, Nil, Init || Z, C] =
      Snoc(init.andThen(g), last > g)

    override def changeTarget[C](f: [X] => (X -> B) => (X -> C)): SinkNAry[->, ||, Nil, Init || Z, C] =
      Snoc(init.changeTarget(f), f(last))

    override def translate[->>[_,_]](f: [X, Y] => (X -> Y) => (X ->> Y)): SinkNAry[->>, ||, Nil, Init || Z, B] =
      Snoc(init.translate(f), f(last))

    override protected def pullback_[->>[_, _], Obj[_]](
      binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (Obj[P], P ->> X, P ->> Y, P -> Q)],
      srcData: [X, Y] => (X -> Y) => Obj[X],
    )(using
      cat: NarrowCategory[Obj, ->>],
    ): Exists[[P] =>> (Obj[P], SourceNAry[->> to Obj, ||, Nil, P, Init || Z], P -> B)] =
      init.pullback_(binaryPullback, srcData) match {
        case Indeed((p, initSrc, f)) =>
          binaryPullback(f, last) match
            case Indeed((pp, f1, f2, g)) =>
              Exists((
                pp,
                SourceNAry.Snoc(
                  initSrc.changeSource([Y] => y => (cat.narrowAndThen(f1, y._1)(using pp, p, y._2), y._2)),
                  (f2, srcData(last))
                ),
                g
              ))
      }

    override def asSource: SourceNAry[[x, y] =>> y -> x, ||, Nil, B, Init || Z] =
      SourceNAry.Snoc(init.asSource, last)

    override def divide[F[_,_], G[_,_]](
      h: [X, Y] => (X -> Y) => Exists[[Q] =>> (F[X, Q], G[Q, Y])],
    ): Exists[[Q] =>> (
      ParN[||, Nil, F, Init || Z, Q],
      SinkNAry[G, ||, Nil, Q, B],
    )] =
      (init.divide(h), h(last)) match
        case (Indeed((fs, gs)), Indeed((f, g))) =>
          Exists((fs ∙ f, SinkNAry.Snoc(gs, g)))

    override def divide3[F[_,_], G[_,_], H[_,_]](
      h: [X, Y] => (X -> Y) => Exists[[P] =>> Exists[[Q] =>> (F[X, P], G[P, Q], H[Q, Y])]],
    ): Exists[[P] =>> Exists[[Q] =>> (
      ParN[||, Nil, F, Init || Z, P],
      ParN[||, Nil, G, P, Q],
      SinkNAry[H, ||, Nil, Q, B]
    )]] =
      (init.divide3(h), h(last)) match
        case (Indeed(Indeed((fs, gs, hs))), Indeed(Indeed((f, g, h)))) =>
          Exists(Exists((fs ∙ f, gs ∙ g, SinkNAry.Snoc(hs, h))))
  }

  def fromProduct[->[_, _], ||[_, _], Nil, As, B](
    p: Items1.Product[||, Nil, [X] =>> X -> B, As],
  ): SinkNAry[->, ||, Nil, As, B] =
    p match
      case Items1.Product.Single(value) => Single(value)
      case Items1.Product.Snoc(init, last) => Snoc(fromProduct(init), last)

}
