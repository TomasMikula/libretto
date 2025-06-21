package libretto.lambda

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed

/** A collection of arrows `A -> Bi`,
 * where `B = Nil || B1 || B2 || ... || Bn`,
 * where `||` associates to the left.
 */
trait SourceNAry[->[_, _], ||[_, _], Nil, A, B] {
  def after[Z](f: Z -> A)(using Semigroupoid[->]): SourceNAry[->, ||, Nil, Z, B]

  def asSink: SinkNAry[[x, y] =>> y -> x, ||, Nil, B, A]

  /** N-ary pushout from binary, generalized in that the arrows
   *  of the resulting sink (n-ary cospan) may be of a different type `->>`.
   */
  def pushout[->>[_, _], Obj[_]](
    binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (X ->> Q, Y ->> Q, P -> Q)],
    tgtData: [X, Y] => (X -> Y) => Obj[Y],
  )(using
    NarrowCategory[->>, Obj],
  ): Exists[[Q] =>> (SinkNAry[->>, ||, Nil, B, Q], A -> Q)]
}

object SourceNAry {
  case class Single[->[_, _], ||[_, _], Nil, A, B](
    f: A -> B,
  ) extends SourceNAry[->, ||, Nil, A, Nil || B] {

    override def after[Z](g: Z -> A)(using s: Semigroupoid[->]): SourceNAry[->, ||, Nil, Z, Nil || B] =
      Single(g > f)

    override def pushout[->>[_,_], Obj[_]](
      binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (X ->> Q, Y ->> Q, P -> Q)],
      tgtData: [X, Y] => (X -> Y) => Obj[Y],
    )(using
      cat: NarrowCategory[->>, Obj],
    ): Exists[[Q] =>> (SinkNAry[->>, ||, Nil, Nil || B, Q], A -> Q)] =
      Exists((
        SinkNAry.Single(cat.id[B](tgtData(f))),
        f
      ))

    override def asSink: SinkNAry[[x, y] =>> y -> x, ||, Nil, Nil || B, A] =
      SinkNAry.Single(f)
  }

  case class Snoc[->[_, _], ||[_, _], Nil, A, Init, Z](
    init: SourceNAry[->, ||, Nil, A, Init],
    last: A -> Z,
  ) extends SourceNAry[->, ||, Nil, A, Init || Z] {

    override def after[A0](f: A0 -> A)(using Semigroupoid[->]): SourceNAry[->, ||, Nil, A0, Init || Z] =
      Snoc(init.after(f), f > last)

    override def pushout[->>[_,_], Obj[_]](
      binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (X ->> Q, Y ->> Q, P -> Q)],
      tgtData: [X, Y] => (X -> Y) => Obj[Y],
    )(using
      cat: NarrowCategory[->>, Obj],
    ): Exists[[Q] =>> (SinkNAry[->>, ||, Nil, Init || Z, Q], A -> Q)] =
      init.pushout(binaryPushout, tgtData) match
        case Indeed((initSink, q)) =>
          binaryPushout(q, last) match
            case Indeed((f1, f2, g)) =>
              Exists((
                SinkNAry.Snoc(
                  initSink.andThen(f1),
                  f2
                ),
                g
              ))

    override def asSink: SinkNAry[[x, y] =>> y -> x, ||, Nil, Init || Z, A] =
      SinkNAry.Snoc(init.asSink, last)
  }
}
