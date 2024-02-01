package libretto.lambda

import libretto.lambda.util.{BiInjective, SourcePos, TypeEqK}

/** Nested tuples with a hole.
 *
 * For example, a structure
 *
 * ```
 * (G[A], (G[B], (◯, G[C])))
 * ```
 *
 * where ◯ is the hole, can be represented as
 *
 * `Spine[**, G, F]` where `F[X] = A ** (B ** (X ** C))`
 *
 * Like [[Focus]], a `Spine` defines a path into a tupled structure,
 * but `Spine` also contains data along the path.
 *
 * @tparam ** the tuple type constructor
 * @tparam G tuple elements ("garnish" hanging from the spine)
 * @tparam F context of the hole
 */
sealed trait Spine[**[_, _], G[_], F[_]] {
  import Spine.*

  def focus: Focus[**, F] =
    this match
      case Id()        => Focus.Id()
      case Fst(fst, _) => Focus.Fst(fst.focus)
      case Snd(_, snd) => Focus.Snd(snd.focus)

  def plugFold[A](a: G[A])(using Zippable[**, G]): G[F[A]] =
    this match
      case Id() => a
      case Fst(fst, snd) => fst.plugFold(a) zip snd
      case Snd(fst, snd) => fst zip snd.plugFold(a)

  def knitFoldMap[H[_]](
    k: Knit[**, F],
    f: [x] => G[x] => H[x],
  )(using BiInjective[**], Zippable[**, H]): H[k.Res]

  def knit(k: Knit[**, F])(using BiInjective[**]): Tupled[**, G, k.Res] =
    knitFoldMap[Tupled[**, G, _]](k, [x] => (gx: G[x]) => Tupled.atom(gx))

  def knitFold(k: Knit[**, F])(using BiInjective[**], Zippable[**, G]): G[k.Res] =
    knitFoldMap[G](k, [x] => (gx: G[x]) => gx)

  def inFst[B](b: G[B]): Spine[**, G, [x] =>> F[x] ** B] =
    Fst(this, b)

  def inSnd[A](a: G[A]): Spine[**, G, [x] =>> A ** F[x]] =
    Snd(a, this)
}

object Spine {
  case class Id[|*|[_, _], G[_]]() extends Spine[|*|, G, [x] =>> x] {
    override def knitFoldMap[H[_]](
      k: Knit[|*|, [x] =>> x],
      f: [x] => G[x] => H[x],
    )(using BiInjective[|*|], Zippable[|*|, H]): H[k.Res] =
      type Fresh
      val ev = k.proveProduct[Fresh]
      type A = ev.T
      type B = ev.value.T
      val impossible: Fresh =:= (A |*| B) = ev.value.value
      throw AssertionError("Impossible for a fresh type to be equal to A |*| B")
  }

  case class Fst[|*|[_, _], G[_], F[_], B](
    fst: Spine[|*|, G, F],
    snd: G[B],
  ) extends Spine[|*|, G, [x] =>> F[x] |*| B] {

    override def knitFoldMap[H[_]](
      k: Knit[|*|, [x] =>> F[x] |*| B],
      f: [x] => G[x] => H[x],
    )(using
      BiInjective[|*|],
      Zippable[|*|, H],
    ): H[k.Res] = {
      k.visit(
        caseKeepFst = [X] => (
          ev1: TypeEqK[[x] =>> F[x] |*| B, [y] =>> X |*| y],
          ev2: k.Res =:= X,
        ) =>
          // impossible, derive contradiction
          val ev3: B =:= Unit    = ev1.at[Unit]    match { case BiInjective[|*|](_, ev) => ev }
          val ev4: B =:= Nothing = ev1.at[Nothing] match { case BiInjective[|*|](_, ev) => ev }
          ev4(ev3.flip(())),
        caseKeepSnd = [Y] => (
          ev1: TypeEqK[[x] =>> F[x] |*| B, [x] =>> x |*| Y],
          ev2: k.Res =:= Y,
        ) =>
          val ev3: B =:= Y     = ev1.at[Any] match { case BiInjective[|*|](_, ev) => ev }
          val ev4: B =:= k.Res = ev3 andThen ev2.flip
          ev4.substituteCo[H](f(snd)),
        caseInFst = [F1[_], Y] => (
          k1: Knit[|*|, F1],
        ) => (
          ev: TypeEqK[[x] =>> F[x] |*| B, [x] =>> F1[x] |*| Y],
          ev1: k.Res =:= (k1.Res |*| Y),
        ) =>
          given TypeEqK[F, F1] =
            TypeEqK.ext[F, F1]([x] => (_: Unit) => ev.at[x] match { case BiInjective[|*|](ev, _) => ev })
          val ev2: B =:= Y =
            ev.at[Any] match { case BiInjective[|*|](_, ev) => ev }
          val fst1: H[k1.Res] = fst.knitFoldMap(k1.from[F], f)
          val snd1: H[Y]      = f(ev2.substituteCo[G](snd))
          ev1.substituteContra[H](fst1 zip snd1),
        caseInSnd = [X, F2[_]] => (
          k2: Knit[|*|, F2],
        ) => (
          ev: TypeEqK[[x] =>> F[x] |*| B, [y] =>> X |*| F2[y]],
          ev1: k.Res =:= (X |*| k2.Res),
        ) =>
          // impossible, derive contradiction
          val injF2 = k2.toFocus.injective
          val bu: B =:= F2[Unit]    = ev.at[Unit]    match { case BiInjective[|*|](_, ev) => ev }
          val bn: B =:= F2[Nothing] = ev.at[Nothing] match { case BiInjective[|*|](_, ev) => ev }
          val un: Unit =:= Nothing  = (bu.flip andThen bn) match { case injF2(ev) => ev }
          un(())
      )
    }
  }

  case class Snd[|*|[_, _], G[_], F[_], A](
    fst: G[A],
    snd: Spine[|*|, G, F],
  ) extends Spine[|*|, G, [x] =>> A |*| F[x]] {

    override def knitFoldMap[H[_]](
      k: Knit[|*|, [x] =>> A |*| F[x]],
      f: [x] => G[x] => H[x],
    )(using BiInjective[|*|], Zippable[|*|, H]): H[k.Res] =
      k.visit(
        caseKeepFst = [X] => (
          ev1: TypeEqK[[y] =>> A |*| F[y], [y] =>> X |*| y],
          ev2: k.Res =:= X,
        ) =>
          val ax: A =:= X     = ev1.at[Any] match { case BiInjective[|*|](ev, _) => ev }
          val ar: A =:= k.Res = ax andThen ev2.flip
          ar.substituteCo(f(fst)),
        caseKeepSnd = [Y] => (
          ev1: TypeEqK[[y] =>> A |*| F[y], [x] =>> x |*| Y],
          ev2: k.Res =:= Y,
        ) =>
          // impossible, derive contradiction
          val ev3: A =:= Nothing = ev1.at[Nothing] match { case BiInjective[|*|](ev, _) => ev }
          val ev4: A =:= Unit    = ev1.at[Unit]    match { case BiInjective[|*|](ev, _) => ev }
          ev3(ev4.flip(())),
        caseInFst = [F1[_], Y] => (
          k1: Knit[|*|, F1],
        ) => (
          ev1: TypeEqK[[y] =>> A |*| F[y], [x] =>> F1[x] |*| Y],
          ev2: k.Res =:= (k1.Res |*| Y),
        ) =>
          // impossible, derive contradiction
          val injF1 = k1.toFocus.injective
          val an: A =:= F1[Nothing] = ev1.at[Nothing] match { case BiInjective[|*|](ev, _) => ev }
          val au: A =:= F1[Unit]    = ev1.at[Unit]    match { case BiInjective[|*|](ev, _) => ev }
          val un: Unit =:= Nothing  = (au.flip andThen an) match { case injF1(ev) => ev }
          un(()),
        caseInSnd = [X, F2[_]] => (
          k2: Knit[|*|, F2],
        ) => (
          ev1: TypeEqK[[y] =>> A |*| F[y], [y] =>> X |*| F2[y]],
          ev2: k.Res =:= (X |*| k2.Res),
        ) =>
          val ev3: A =:= X = ev1.at[Any] match { case BiInjective[|*|](ev, _) => ev }
          given TypeEqK[F, F2] =
            TypeEqK.ext[F, F2]([y] => (_: Unit) => ev1.at[y] match { case BiInjective[|*|](_, ev) => ev} )
          val fst1: H[X]      = f(ev3.substituteCo(fst))
          val snd1: H[k2.Res] = snd.knitFoldMap(k2.from[F], f)
          ev2.substituteContra[H](fst1 zip snd1),
      )
  }
}
