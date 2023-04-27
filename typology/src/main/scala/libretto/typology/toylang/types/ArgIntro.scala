package libretto.typology.toylang.types

import libretto.typology.kinds._

/** Transforms type arguments from kind `K` into `L` by introducing additional type arguments.
 *  Used as a vehicle to deliver (partial) type arguments into a type function `L ->> M`.
 *
 * @tparam K the kind before adding type arguments
 * @tparam L the kind after adding type arguments (i.e. `K` interspersed with additional type arguments)
 * @tparam TA the type of type arguments, parameterized by kind
 */
sealed trait ArgIntro[TA[_], K, L] {
  import ArgIntro._

  given inKind: Kind[K]
  given outKind: ProperKind[L]

  def from[J](using ev: J =:= K): ArgIntro[TA, J, L] =
    ev.substituteContra[ArgIntro[TA, *, L]](this)

  def to[M](using ev: L =:= M): ArgIntro[TA, K, M] =
    ev.substituteCo[ArgIntro[TA, K, *]](this)
}

object ArgIntro {
  case class WrapArg[TA[_], K](arg: TA[K])(using
    val outputKind: OutputKind[K],
  ) extends ArgIntro[TA, ○, K] {
    override def inKind: Kind[○] = summon[Kind[○]]
    override def outKind: ProperKind[K] = outputKind.properKind
  }

  case class Id[TA[_], K]()(using k: ProperKind[K]) extends ArgIntro[TA, K, K] {
    override def inKind: Kind[K] = k.kind
    override def outKind: ProperKind[K] = k
  }

  case class Par[TA[_], K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
    f1: ArgIntro[TA, K1, L1],
    f2: ArgIntro[TA, K2, L2],
  ) extends ArgIntro[TA, K1 × K2, L1 × L2] {
    override def inKind: Kind[K1 × K2] = (ProperKind[K1] × ProperKind[K2]).kind
    override def outKind: ProperKind[L1 × L2] = ProperKind[L1] × ProperKind[L2]
  }

  case class IntroFst[TA[_], K, L, M](
    args: ArgIntro[TA, ○, K],
    f: ArgIntro[TA, L, M],
  )(using
    val properInKind: ProperKind[L]
  ) extends ArgIntro[TA, L, K × M] {
    override def inKind: Kind[L]            = ProperKind[L].kind
    override def outKind: ProperKind[K × M] = args.outKind × f.outKind
  }

  case class IntroSnd[TA[_], K: ProperKind, L, M](
    f: ArgIntro[TA, K, L],
    args: ArgIntro[TA, ○, M],
  ) extends ArgIntro[TA, K, L × M] {
    override def inKind: Kind[K]            = ProperKind[K].kind
    override def outKind: ProperKind[L × M] = f.outKind × args.outKind
  }

  case class IntroBoth[TA[_], K, L](
    args1: ArgIntro[TA, ○, K],
    args2: ArgIntro[TA, ○, L],
  ) extends ArgIntro[TA, ○, K × L] {
    override def inKind: Kind[○] = summon[Kind[○]]
    override def outKind: ProperKind[K × L] = args1.outKind × args2.outKind
  }

  def wrapArg[TA[_], K: OutputKind](arg: TA[K]): ArgIntro[TA, ○, K] =
    WrapArg(arg)

  def id[TA[_], K: ProperKind]: ArgIntro[TA, K, K] =
    Id()

  def par[TA[_], K1: ProperKind, K2: ProperKind, L1: ProperKind, L2: ProperKind](
    f1: ArgIntro[TA, K1, L1],
    f2: ArgIntro[TA, K2, L2],
  ): ArgIntro[TA, K1 × K2, L1 × L2] =
    Par(f1, f2)

  def fst[TA[_], K: ProperKind, L: ProperKind, M: ProperKind](f: ArgIntro[TA, K, L]): ArgIntro[TA, K × M, L × M] =
    par(f, id[TA, M])

  def snd[TA[_], K: ProperKind, L: ProperKind, M: ProperKind](g: ArgIntro[TA, L, M]): ArgIntro[TA, K × L, K × M] =
    par(id[TA, K], g)

  def introFst[TA[_], K, L: ProperKind](args: ArgIntro[TA, ○, K]): ArgIntro[TA, L, K × L] =
    IntroFst(args, Id())

  def introFst[TA[_], K, L: ProperKind, M](args: ArgIntro[TA, ○, K], f: ArgIntro[TA, L, M]): ArgIntro[TA, L, K × M] =
    IntroFst(args, f)

  def introSnd[TA[_], K: ProperKind, L](args: ArgIntro[TA, ○, L]): ArgIntro[TA, K, K × L] =
    IntroSnd(Id(), args)

  def introSnd[TA[_], K: ProperKind, L, M](f: ArgIntro[TA, K, L], args: ArgIntro[TA, ○, M]): ArgIntro[TA, K, L × M] =
    IntroSnd(f, args)

  def introBoth[TA[_], K, L](args1: ArgIntro[TA, ○, K], args2: ArgIntro[TA, ○, L]): ArgIntro[TA, ○, K × L] =
    IntroBoth(args1, args2)

  def wrapArgFst[TA[_], K: OutputKind, L: ProperKind](arg: TA[K]): ArgIntro[TA, L, K × L] =
    introFst(wrapArg(arg))

  def wrapArgSnd[TA[_], K: ProperKind, L: OutputKind](arg: TA[L]): ArgIntro[TA, K, K × L] =
    introSnd(wrapArg(arg))

  def unwrap[TA[_], K](i: ArgIntro[TA, ○, K])(using k: OutputKind[K]): TA[K] =
    i match {
      case WrapArg(a) =>
        a
      case other =>
        // TODO: prove using OutputKind[K], instead of throwing an exception
        throw new AssertionError(s"didn't expect $i to produce an OutputKind")
    }

  def deriveId[TA[_], K, L](i: ArgIntro[TA, K, L])(using k: ProperKind[K], l: OutputKind[L]): K =:= L =
    i match {
      case Id() =>
        summon[K =:= L]
      case other =>
        // TODO: derive, instead of asserting
        throw new AssertionError(s"didn't expect $other")
    }
}
