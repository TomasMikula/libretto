package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, TypeEqK}

class CoproductPartitioning[->[_, _], **[_, _], ++[_, _]](
  lName: String,
  rName: String,
)(using
  cat: SemigroupalCategory[->, **],
  cocat: CocartesianSemigroupalCategory[->, ++],
  distribution: Distribution[->, **, ++],
  inj: BiInjective[++], // although unused, is needed for the typecast in `sameAs` to be sound
) {
  import cocat.{either, injectL, injectR}

  def Inl[A, B]: Extractor[->, **, A ++ B, A] =
    Extractor(new CoproductPartitioning[A, B], Side.Left())

  def Inr[A, B]: Extractor[->, **, A ++ B, B] =
    Extractor(new CoproductPartitioning[A, B], Side.Right())

  private final class CoproductPartitioning[A, B] extends Partitioning[->, **, A ++ B] {

    override type Partition[P] = Side[A ++ B, P]

    override def compileAt[F[_], G[_], R](
      pos: Focus[**, F],
      handle: [X] => (x: Partition[X]) => G[F[X] -> R],
    )(using
      Applicative[G],
    ): G[F[A ++ B] -> R] = {
      val ha: G[F[A] -> R] = handle(Side.Left())
      val hb: G[F[B] -> R] = handle(Side.Right())
      (ha zip hb).map { case (ha, hb) =>
        cat.andThen(
          distribution.distF(using pos),
          either(ha, hb)
        )
      }
    }

    override def reinject[P](p: Partition[P]): P -> (A ++ B) =
      p match
        case Side.Left() => injectL
        case Side.Right() => injectR

    override def sameAs(that: Partitioning[->, **, A ++ B]): Option[TypeEqK[this.Partition, that.Partition]] =
      that match
        case that1: (CoproductPartitioning[a, b] & that.type) =>
          Some(
            TypeEqK.refl[this.Partition]
              .asInstanceOf[TypeEqK[this.Partition, that.Partition]]
          )
        case _ =>
          None

    override def samePartition[P, Q](p: Partition[P], q: Partition[Q]): Option[P =:= Q] =
      (p, q) match
        case (Side.Left(), Side.Left()) => Some(summon[A =:= A])
        case (Side.Right(), Side.Right()) => Some(summon[B =:= B])
        case _ => None

    override def showPartition[P](p: Partition[P]): String =
      p match
        case Side.Left()  => lName
        case Side.Right() => rName

    override def isTotal[P](p: Partition[P]): Option[(A ++ B) -> P] =
      libretto.lambda.UnhandledCase.raise(s"CoproductPartitioning.isTotal")
  }

  private enum Side[T, S]:
    case Left[A, B]()  extends Side[A ++ B, A]
    case Right[A, B]() extends Side[A ++ B, B]
}
