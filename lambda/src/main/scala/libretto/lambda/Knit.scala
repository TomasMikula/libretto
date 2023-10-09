package libretto.lambda

import libretto.lambda.Projection
import libretto.lambda.util.{Exists, ExistsK, SourcePos}

sealed trait Knit[**[_, _], F[_]] {
  type Res

  def inFst[Y]: Knitted[**, [x] =>> F[x] ** Y, Res ** Y] =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def inSnd[X]: Knitted[**, [x] =>> X ** F[x], X ** Res] =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def toProjection[X]: Projection[**, F[X], Res]

  def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> F[X] =:= (a ** b)]]

  def at[G[_]](g: Focus[**, G]): Knitted[**, [x] =>> G[F[x]], G[Res]] =
    g match
      case Focus.Id() =>
        this
      case g: Focus.Fst[p, f1, b] =>
        this.at(g.i).inFst[b]
      case g: Focus.Snd[p, f2, a] =>
        this.at(g.i).inSnd[a]
}

object Knit {
  case class KeepFst[**[_, _], A]() extends Knit[**, [x] =>> A ** x] {
    override type Res = A

    override def toProjection[X]: Projection[**, A ** X, A] =
      Projection.discardSnd

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> A ** X =:= a ** b]] =
      Exists(Exists(summon[(A ** X) =:= (A ** X)]))
  }

  case class KeepSnd[**[_, _], B]() extends Knit[**, [x] =>> x ** B] {
    override type Res = B

    override def toProjection[X]: Projection[**, X ** B, B] =
      Projection.discardFst

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> X ** B =:= a ** b]] =
      Exists(Exists(summon[(X ** B) =:= (X ** B)]))
  }

  case class InFst[**[_, _], F[_], B](k: Knit[**, F]) extends Knit[**, [x] =>> F[x] ** B] {
    override type Res = k.Res ** B

    override def toProjection[X]: Projection[**, F[X] ** B, Res] =
      k.toProjection[X].inFst[B]

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> F[X] ** B =:= a ** b]] =
      Exists(Exists(summon[(F[X] ** B) =:= (F[X] ** B)]))
  }

  case class InSnd[**[_, _], A, G[_]](k: Knit[**, G]) extends Knit[**, [x] =>> A ** G[x]] {
    override type Res = A ** k.Res

    override def toProjection[X]: Projection[**, A ** G[X], Res] =
      k.toProjection[X].inSnd[A]

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> A ** G[X] =:= a ** b]] =
      Exists(Exists(summon[(A ** G[X]) =:= (A ** G[X])]))
  }
}

type Knitted[**[_, _], F[_], F0] =
  Knit[**, F] { type Res = F0 }

object Knitted {
  def functional[**[_, _], F[_], F1, F2](
    k1: Knitted[**, F, F1],
    k2: Knitted[**, F, F2],
  ): F1 =:= F2 =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def fromProjection[**[_, _], P, Q](p: Projection[**, P, Q]): Option[ExistsK[[F[_]] =>> Knitted[**, F, Q]]] =
    p match
      case Projection.Id() =>
        None
      case p: Projection.DiscardFst[prod, p1, p2, q2] =>
        summon[q2 =:= Q]
        p.p2 match
          case Projection.Id()               => Some(ExistsK(keepSnd[**, Q]))
          case _: Projection.Proper[p, x, y] => None
      case Projection.DiscardSnd(p1) => throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Projection.Fst(p1) => throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Projection.Snd(p2) => throw NotImplementedError(s"at ${summon[SourcePos]}")
      case Projection.Both(p1, p2) => throw NotImplementedError(s"at ${summon[SourcePos]}")


  def keepFst[**[_, _], A]: Knitted[**, [x] =>> A ** x, A] =
    Knit.KeepFst()

  def keepSnd[**[_, _], B]: Knitted[**, [x] =>> x ** B, B] =
    Knit.KeepSnd()
}
