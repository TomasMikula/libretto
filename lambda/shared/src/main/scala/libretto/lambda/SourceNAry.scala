package libretto.lambda

import libretto.lambda.util.Exists
import libretto.lambda.util.Exists.Indeed

/** A collection of arrows `A -> Bi`,
 * where `B = Nil || B1 || B2 || ... || Bn`,
 * where `||` associates to the left.
 */
trait SourceNAry[->[_, _], ||[_, _], Nil, A, B] {
  import SourceNAry.from

  def after[Z](f: Z -> A)(using Semigroupoid[->]): SourceNAry[->, ||, Nil, Z, B]

  def changeSource[Z](f: [Y] => (A -> Y) => (Z -> Y)): SourceNAry[->, ||, Nil, Z, B]

  def translate[->>[_, _]](f: [X, Y] => (X -> Y) => (X ->> Y)): SourceNAry[->>, ||, Nil, A, B]

  def asSink: SinkNAry[[x, y] =>> y -> x, ||, Nil, B, A]

  /** N-ary pushout from binary, generalized in that the arrows
   *  of the resulting sink (n-ary cospan) may be of a different type `->>`.
   */
  def pushout[->>[_, _], Obj[_]](
    binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (Obj[Q], X ->> Q, Y ->> Q, P -> Q)],
    tgtData: [X, Y] => (X -> Y) => Obj[Y],
  )(using
    NarrowCategory[Obj, ->>],
  ): Exists[[Q] =>> (SinkNAry[->>, ||, Nil, B, Q], A -> Q)] =
    pushout_(binaryPushout, tgtData) match
      case Indeed((_, sink, q)) =>
        Indeed((sink.translate[->>]([X, Y] => f => f._2), q))

  protected def pushout_[->>[_, _], Obj[_]](
    binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (Obj[Q], X ->> Q, Y ->> Q, P -> Q)],
    tgtData: [X, Y] => (X -> Y) => Obj[Y],
  )(using
    NarrowCategory[Obj, ->>],
  ): Exists[[Q] =>> (Obj[Q], SinkNAry[->> from Obj, ||, Nil, B, Q], A -> Q)]
}

object SourceNAry {
  private[SourceNAry] infix type from[->[_, _], Src[_]] = [A, B] =>> (Src[A], A -> B)

  case class Single[->[_, _], ||[_, _], Nil, A, B](
    f: A -> B,
  ) extends SourceNAry[->, ||, Nil, A, Nil || B] {

    override def after[Z](g: Z -> A)(using s: Semigroupoid[->]): SourceNAry[->, ||, Nil, Z, Nil || B] =
      Single(g > f)

    override def changeSource[Z](g: [Y] => (A -> Y) => (Z -> Y)): SourceNAry[->, ||, Nil, Z, Nil || B] =
      Single(g(f))

    override def translate[->>[_,_]](g: [X, Y] => (X -> Y) => (X ->> Y)): SourceNAry[->>, ||, Nil, A, Nil || B] =
      Single(g(f))

    override protected def pushout_[->>[_,_], Obj[_]](
      binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (Obj[Q], X ->> Q, Y ->> Q, P -> Q)],
      tgtData: [X, Y] => (X -> Y) => Obj[Y],
    )(using
      cat: NarrowCategory[Obj, ->>],
    ): Exists[[Q] =>> (Obj[Q], SinkNAry[->> from Obj, ||, Nil, Nil || B, Q], A -> Q)] =
      given b: Obj[B] = tgtData(f)
      Exists((
        b,
        SinkNAry.Single((b, cat.id[B])),
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

    override def changeSource[B](f: [Y] => (A -> Y) => (B -> Y)): SourceNAry[->, ||, Nil, B, Init || Z] =
      Snoc(init.changeSource(f), f(last))

    override def translate[->>[_,_]](f: [X, Y] => (X -> Y) => (X ->> Y)): SourceNAry[->>, ||, Nil, A, Init || Z] =
      Snoc(init.translate(f), f(last))

    override protected def pushout_[->>[_,_], Obj[_]](
      binaryPushout: [P, X, Y] => (P -> X, P -> Y) => Exists[[Q] =>> (Obj[Q], X ->> Q, Y ->> Q, P -> Q)],
      tgtData: [X, Y] => (X -> Y) => Obj[Y],
    )(using
      cat: NarrowCategory[Obj, ->>],
    ): Exists[[Q] =>> (Obj[Q], SinkNAry[->> from Obj, ||, Nil, Init || Z, Q], A -> Q)] =
      init.pushout_(binaryPushout, tgtData) match
        case Indeed((q, initSink, f)) =>
          binaryPushout(f, last) match
            case Indeed((r, g1, g2, g)) =>
              Exists((
                r,
                SinkNAry.Snoc(
                  initSink.changeTarget([X] => x => (x._1, cat.narrowAndThen(x._2, g1)(using x._1, q, r))),
                  (tgtData(last), g2)
                ),
                g
              ))

    override def asSink: SinkNAry[[x, y] =>> y -> x, ||, Nil, Init || Z, A] =
      SinkNAry.Snoc(init.asSink, last)
  }
}
