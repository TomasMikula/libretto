package libretto.lambda

import libretto.lambda.util.Exists

/** A collection of arrows `Ai -> B`,
 * where `A = Nil || A1 || A2 || ... || An`,
 * where `||` associates to the left.
 */
trait SinkNAry[->[_, _], ||[_, _], Nil, A, B] {
  def andThen[C](g: B -> C)(using Semigroupoid[->]): SinkNAry[->, ||, Nil, A, C]

  def asSource: SourceNAry[[x, y] =>> y -> x, ||, Nil, B, A]

  /** N-ary pullback from binary, generalized in that the arrows
   *  of the resulting source (n-ary span) may be of a different type `->>`.
   */
  def pullback[->>[_, _], Obj[_]](
    binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (P ->> X, P ->> Y, P -> Q)],
    srcData: [X, Y] => (X -> Y) => Obj[X],
  )(using
    NarrowCategory[->>, Obj],
  ): Exists[[P] =>> (SourceNAry[->>, ||, Nil, P, A], P -> B)]
}

object SinkNAry {
  case class Single[->[_, _], ||[_, _], Nil, A, B](
    f: A -> B,
  ) extends SinkNAry[->, ||, Nil, Nil || A, B] {

    override def andThen[C](g: B -> C)(using Semigroupoid[->]): SinkNAry[->, ||, Nil, Nil || A, C] =
      Single(f > g)

    override def pullback[->>[_,_], Obj[_]](
      binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (P ->> X, P ->> Y, P -> Q)],
      srcData: [X, Y] => (X -> Y) => Obj[X],
    )(using
      cat: NarrowCategory[->>, Obj],
    ): Exists[[P] =>> (SourceNAry[->>, ||, Nil, P, Nil || A], P -> B)] =
      Exists((
        SourceNAry.Single(cat.id[A](srcData(f))),
        f
      ))

    override def asSource: SourceNAry[[x, y] =>> y -> x, ||, Nil, B, Nil || A] =
      SourceNAry.Single(f)
  }

  case class Snoc[->[_, _], ||[_, _], Nil, Init, Z, B](
    init: SinkNAry[->, ||, Nil, Init, B],
    last: Z -> B,
  ) extends SinkNAry[->, ||, Nil, Init || Z, B] {

    override def andThen[C](g: B -> C)(using Semigroupoid[->]): SinkNAry[->, ||, Nil, Init || Z, C] =
      Snoc(init.andThen(g), last > g)

    override def pullback[->>[_,_], Obj[_]](
      binaryPullback: [X, Y, Q] => (X -> Q, Y -> Q) => Exists[[P] =>> (P ->> X, P ->> Y, P -> Q)],
      srcData: [X, Y] => (X -> Y) => Obj[X],
    )(using
      cat: NarrowCategory[->>, Obj],
    ): Exists[[P] =>> (SourceNAry[->>, ||, Nil, P, Init || Z], P -> B)] =
      init.pullback(binaryPullback, srcData) match {
        case Exists.Some((initSrc, p)) =>
          binaryPullback(p, last) match
            case Exists.Some((f1, f2, g)) =>
              Exists((
                SourceNAry.Snoc(
                  initSrc.after(f1),
                  f2
                ),
                g
              ))
      }

    override def asSource: SourceNAry[[x, y] =>> y -> x, ||, Nil, B, Init || Z] =
      SourceNAry.Snoc(init.asSource, last)
  }
}
