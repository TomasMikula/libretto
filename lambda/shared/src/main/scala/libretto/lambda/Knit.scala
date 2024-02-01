package libretto.lambda

import libretto.lambda.Projection
import libretto.lambda.util.{BiInjective, Exists, ExistsK, SourcePos, TypeEqK}

sealed trait Knit[**[_, _], F[_]] {
  type Res

  def from[E[_]](using ev: TypeEqK[E, F]): Knitted[**, E, Res] =
    ev.flip.subst[[f[_]] =>> Knitted[**, f, Res]](this)

  def to[R](using ev: Res =:= R): Knitted[**, F, R] =
    ev.substituteCo[[r] =>> Knitted[**, F, r]](this)

  def inFst[Y]: Knitted[**, [x] =>> F[x] ** Y, Res ** Y] =
    Knitted.inFst(this)

  def inSnd[X]: Knitted[**, [x] =>> X ** F[x], X ** Res] =
    Knitted.inSnd(this)

  def toProjection[X]: Projection[**, F[X], Res]

  def toFocus: Focus[**, F]

  def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> F[X] =:= (a ** b)]]

  def at[G[_]](g: Focus[**, G]): Knitted[**, [x] =>> G[F[x]], G[Res]] =
    g match
      case Focus.Id() =>
        this
      case g: Focus.Fst[p, f1, b] =>
        this.at(g.i).inFst[b]
      case g: Focus.Snd[p, f2, a] =>
        this.at(g.i).inSnd[a]

  def visit[R](
    caseKeepFst: [X] => (TypeEqK[F, **[X, *]], Res =:= X) => R,
    caseKeepSnd: [Y] => (TypeEqK[F, **[*, Y]], Res =:= Y) => R,
    caseInFst: [F1[_], Y] => (k: Knit[**, F1]) => (ev: TypeEqK[F, [x] =>> F1[x] ** Y], ev1: Res =:= (k.Res ** Y)) => R,
    caseInSnd: [X, F2[_]] => (k: Knit[**, F2]) => (ev: TypeEqK[F, [y] =>> X ** F2[y]], ev1: Res =:= (X ** k.Res)) => R,
  ): R
}

object Knit {
  case class KeepFst[**[_, _], A]() extends Knit[**, [x] =>> A ** x] {
    override type Res = A

    override def toProjection[X]: Projection[**, A ** X, A] =
      Projection.discardSnd

    override def toFocus: Focus[**, [x] =>> A ** x] =
      Focus.snd

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> A ** X =:= a ** b]] =
      Exists(Exists(summon[(A ** X) =:= (A ** X)]))

    override def visit[R](
      caseKeepFst: [X] => (TypeEqK[**[A, *], **[X, *]], Res =:= X) => R,
      caseKeepSnd: [Y] => (TypeEqK[**[A, *], **[*, Y]], Res =:= Y) => R,
      caseInFst: [F1[_], Y] => (k: Knit[**, F1]) => (ev: TypeEqK[**[A, *], [x] =>> F1[x] ** Y], ev1: Res =:= (k.Res ** Y)) => R,
      caseInSnd: [X, F2[_]] => (k: Knit[**, F2]) => (ev: TypeEqK[**[A, *], [y] =>> X ** F2[y]], ev1: Res =:= (X ** k.Res)) => R,
    ): R =
      caseKeepFst[A](summon, summon)
  }

  case class KeepSnd[**[_, _], B]() extends Knit[**, [x] =>> x ** B] {
    override type Res = B

    override def toProjection[X]: Projection[**, X ** B, B] =
      Projection.discardFst

    override def toFocus: Focus[**, [x] =>> x ** B] =
      Focus.fst

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> X ** B =:= a ** b]] =
      Exists(Exists(summon[(X ** B) =:= (X ** B)]))

    override def visit[R](
      caseKeepFst: [X] => (TypeEqK[**[*, B], **[X, *]], Res =:= X) => R,
      caseKeepSnd: [Y] => (TypeEqK[**[*, B], **[*, Y]], Res =:= Y) => R,
      caseInFst: [F1[_], Y] => (k: Knit[**, F1]) => (ev: TypeEqK[**[*, B], [x] =>> F1[x] ** Y], ev1: Res =:= (k.Res ** Y)) => R,
      caseInSnd: [X, F2[_]] => (k: Knit[**, F2]) => (ev: TypeEqK[**[*, B], [y] =>> X ** F2[y]], ev1: Res =:= (X ** k.Res)) => R,
    ): R =
      caseKeepSnd[B](summon, summon)
  }

  sealed abstract case class InFst[**[_, _], F[_], B](k: Knit[**, F]) extends Knit[**, [x] =>> F[x] ** B] {
    override type Res = k.Res ** B

    override def toProjection[X]: Projection[**, F[X] ** B, Res] =
      k.toProjection[X].inFst[B]

    override def toFocus: Focus[**, [x] =>> F[x] ** B] =
      Focus.fst(k.toFocus)

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> F[X] ** B =:= a ** b]] =
      Exists(Exists(summon[(F[X] ** B) =:= (F[X] ** B)]))

    override def visit[R](
      caseKeepFst: [X] => (TypeEqK[[x] =>> F[x] ** B, **[X, *]], Res =:= X) => R,
      caseKeepSnd: [Y] => (TypeEqK[[x] =>> F[x] ** B, **[*, Y]], Res =:= Y) => R,
      caseInFst: [F1[_], Y] => (k: Knit[**, F1]) => (ev: TypeEqK[[x] =>> F[x] ** B, [x] =>> F1[x] ** Y], ev1: Res =:= (k.Res ** Y)) => R,
      caseInSnd: [X, F2[_]] => (k: Knit[**, F2]) => (ev: TypeEqK[[x] =>> F[x] ** B, [y] =>> X ** F2[y]], ev1: Res =:= (X ** k.Res)) => R,
    ): R =
      caseInFst[F, B](k)(summon, summon)
  }

  class InFstImpl[**[_, _], F[_], B, A](override val k: Knitted[**, F, A]) extends InFst[**, F, B](k)

  sealed abstract case class InSnd[**[_, _], A, G[_]](k: Knit[**, G]) extends Knit[**, [y] =>> A ** G[y]] {
    override type Res = A ** k.Res

    override def toProjection[X]: Projection[**, A ** G[X], Res] =
      k.toProjection[X].inSnd[A]

    override def toFocus: Focus[**, [y] =>> A ** G[y]] =
      Focus.snd(k.toFocus)

    override def proveProduct[X]: Exists[[a] =>> Exists[[b] =>> A ** G[X] =:= a ** b]] =
      Exists(Exists(summon[(A ** G[X]) =:= (A ** G[X])]))

    override def visit[R](
      caseKeepFst: [X] => (TypeEqK[[y] =>> A ** G[y], **[X, *]], Res =:= X) => R,
      caseKeepSnd: [Y] => (TypeEqK[[y] =>> A ** G[y], **[*, Y]], Res =:= Y) => R,
      caseInFst: [F1[_], Y] => (k: Knit[**, F1]) => (ev: TypeEqK[[y] =>> A ** G[y], [x] =>> F1[x] ** Y], ev1: Res =:= (k.Res ** Y)) => R,
      caseInSnd: [X, F2[_]] => (k: Knit[**, F2]) => (ev: TypeEqK[[y] =>> A ** G[y], [y] =>> X ** F2[y]], ev1: Res =:= (X ** k.Res)) => R,
    ): R =
      caseInSnd[A, G](k)(summon, summon)
  }

  class InSndImpl[**[_, _], A, G[_], B](override val k: Knitted[**, G, B]) extends InSnd[**, A, G](k)
}

type Knitted[**[_, _], F[_], F0] =
  Knit[**, F] { type Res = F0 }

object Knitted {
  def functional[**[_, _], F[_], F1, F2](
    k1: Knitted[**, F, F1],
    k2: Knitted[**, F, F2],
  ): F1 =:= F2 =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def fromProjection[**[_, _], P, Q](p: Projection[**, P, Q])(using
    BiInjective[**],
  ): Option[ExistsK[[F[_]] =>> Knitted[**, F, Q]]] =
    p match
      case Projection.Id() =>
        None
      case p: Projection.Proper[pr, p, q] =>
        p.startsFromPair match {
          case Exists.Some(Exists.Some(ev)) =>
            fromProjectionProper(ev.substituteCo[[x] =>> Projection.Proper[**, x, Q]](p))
        }

  private def fromProjectionProper[**[_, _], P1, P2, Q](
    p: Projection.Proper[**, P1 ** P2, Q],
  )(using
    BiInjective[**],
  ): Option[ExistsK[[F[_]] =>> Knitted[**, F, Q]]] = {
    import libretto.lambda.{Projection as P}

    p.fromPair[P1, P2].switch(
      caseDiscardFst = p2 => {
        p2 match
          case P.Id()               => Some(ExistsK(keepSnd[**, Q]))
          case _: P.Proper[p, x, y] => None // Knit cannot represent multiple holes
      },
      caseDiscardSnd = p1 => {
        p1 match
          case P.Id()               => Some(ExistsK(keepFst[**, Q]))
          case _: P.Proper[p, x, y] => None // Knit cannot represent multiple holes
      },
      casePar = [Q1, Q2] => (ev: Q =:= (Q1 ** Q2)) ?=> (p: P.Par[**, P1, P2, Q1, Q2]) => {
        p match
          case P.Fst(p1) =>
            fromProjection(p1)
              .map { case e @ ExistsK.Some(k1) =>
                ExistsK[[f[_]] =>> Knitted[**, f, Q], [x] =>> e.T[x] ** Q2](
                  k1.inFst[Q2].to[Q](using ev.flip)
                )
              }
          case P.Snd(p2) =>
            fromProjection(p2)
              .map { case e @ ExistsK.Some(k2) =>
                ExistsK[[f[_]] =>> Knitted[**, f, Q], [x] =>> Q1 ** e.T[x]](
                  k2.inSnd[Q1].to[Q](using ev.flip)
                )
              }
          case P.Both(p1, p2) =>
            None // Knit cannot represent multiple holes
      },
    )
  }

  def keepFst[**[_, _], A]: Knitted[**, [x] =>> A ** x, A] =
    Knit.KeepFst()

  def keepSnd[**[_, _], B]: Knitted[**, [x] =>> x ** B, B] =
    Knit.KeepSnd()

  def inSnd[**[_, _], A, F2[_], B](k: Knitted[**, F2, B]): Knitted[**, [y] =>> A ** F2[y], A ** B] =
    Knit.InSndImpl(k)

  def inFst[**[_, _], F1[_], B, A](k: Knitted[**, F1, A]): Knitted[**, [x] =>> F1[x] ** B, A ** B] =
    Knit.InFstImpl(k)
}
