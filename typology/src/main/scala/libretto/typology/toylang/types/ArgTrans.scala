package libretto.typology.toylang.types

import libretto.typology.kinds._

/** Transforms type arguments from kind `K` to kind `L` by transformation functions `F[x, y]`.
 *
 * @tparam K the kind before transforming (some of the) type arguments
 * @tparam L the kind after transforming (some of the) type arguments
 * @tparam F the type of transformations, parameterized by kinds
 */
sealed trait ArgTrans[F[_, _], K, L] {
  import ArgTrans._

  given inKind: Kind[K]
  given outKind: ProperKind[L]

  def fst[M](using ProperKind[K], ProperKind[M]): ArgTrans[F, K × M, L × M] =
    ArgTrans.fst(this)

  def snd[J](using ProperKind[J], ProperKind[K]): ArgTrans[F, J × K, J × L] =
    ArgTrans.snd(this)
}

object ArgTrans {
  case class Wrap[F[_, _], K, L](f: F[K, L])(using
    k: Kind[K],
    val outputKind: OutputKind[L],
  ) extends ArgTrans[F, K, L] {
    override def inKind: Kind[K] = k
    override def outKind: ProperKind[L] = outputKind.properKind
  }

  case class Par[F[_, _], K1: ProperKind, K2: ProperKind, L1, L2](
    f1: ArgTrans[F, K1, L1],
    f2: ArgTrans[F, K2, L2],
  ) extends ArgTrans[F, K1 × K2, L1 × L2] {
    override def inKind: Kind[K1 × K2] = (ProperKind[K1] × ProperKind[K2]).kind
    override def outKind: ProperKind[L1 × L2] = f1.outKind × f2.outKind
  }

  // TODO: replace by Par + Id
  case class Fst[F[_, _], K: ProperKind, L, M: ProperKind](f: ArgTrans[F, K, L]) extends ArgTrans[F, K × M, L × M] {
    override def inKind: Kind[K × M] = (ProperKind[K] × ProperKind[M]).kind
    override def outKind: ProperKind[L × M] = f.outKind × ProperKind[M]
  }

  // TODO: replace by Par + Id
  case class Snd[F[_, _], K: ProperKind, L: ProperKind, M](f: ArgTrans[F, L, M]) extends ArgTrans[F, K × L, K × M] {
    override def inKind: Kind[K × L] = (ProperKind[K] × ProperKind[L]).kind
    override def outKind: ProperKind[K × M] = ProperKind[K] × f.outKind

    def in1Kind: ProperKind[K] = ProperKind[K]
    def in2Kind: ProperKind[L] = ProperKind[L]
    def out2Kind: ProperKind[M] = f.outKind
  }

  case class IntroFst[F[_, _], K, L: ProperKind](f: ArgTrans[F, ○, K]) extends ArgTrans[F, L, K × L] {
    override def inKind: Kind[L] = ProperKind[L].kind
    override def outKind: ProperKind[K × L] = f.outKind × ProperKind[L]
  }

  case class IntroBoth[F[_, _], K, L](f: ArgTrans[F, ○, K], g: ArgTrans[F, ○, L]) extends ArgTrans[F, ○, K × L] {
    override def inKind: Kind[○] = summon[Kind[○]]
    override def outKind: ProperKind[K × L] = f.outKind × g.outKind
  }

  def apply[F[_, _], K: Kind, L: OutputKind](f: F[K, L]): ArgTrans[F, K, L] =
    wrap(f)

  def wrap[F[_, _], K: Kind, L: OutputKind](f: F[K, L]): ArgTrans[F, K, L] =
    Wrap(f)

  def par[F[_, _], K1: ProperKind, K2: ProperKind, L1, L2](
    f1: ArgTrans[F, K1, L1],
    f2: ArgTrans[F, K2, L2],
  ): ArgTrans[F, K1 × K2, L1 × L2] =
    Par(f1, f2)

  def fst[F[_, _], K: ProperKind, L, M: ProperKind](f: ArgTrans[F, K, L]): ArgTrans[F, K × M, L × M] =
    Fst(f)

  def snd[F[_, _], K: ProperKind, L: ProperKind, M](f: ArgTrans[F, L, M]): ArgTrans[F, K × L, K × M] =
    Snd(f)

  def introFst[F[_, _], K, L: ProperKind](f: ArgTrans[F, ○, K]): ArgTrans[F, L, K × L] =
    IntroFst(f)

  def introBoth[F[_, _], K, L](f: ArgTrans[F, ○, K], g: ArgTrans[F, ○, L]): ArgTrans[F, ○, K × L] =
    IntroBoth(f, g)

  def unwrap[F[_, _], K, L](f: ArgTrans[F, K, L])(using l: OutputKind[L]): F[K, L] =
    f match {
      case Wrap(f) =>
        f
      case other =>
        // TODO: prove using OutputKind[K], instead of throwing an exception
        throw new AssertionError(s"didn't expect $f to produce an OutputKind")
    }
}
