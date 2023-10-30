package libretto.lambda

import libretto.lambda.util.{BiInjective, Exists, Injective}

sealed trait Focus[|*|[_, _], F[_]] {
  import Focus.*

  def compose[G[_]](that: Focus[|*|, G]): Focus[|*|, [x] =>> F[G[x]]] =
    this match {
      case Id()   => that
      case Fst(i) => (i compose that).inFst
      case Snd(i) => (i compose that).inSnd
    }

  def inFst[B]: Focus[|*|, [x] =>> F[x] |*| B] =
    Focus.fst(this)

  def inSnd[A]: Focus[|*|, [x] =>> A |*| F[x]] =
    Focus.snd(this)

  def injective(using BiInjective[|*|]): Injective[F]
}

object Focus {
  case class Id[|*|[_, _]]() extends Focus[|*|, [x] =>> x]:
    override def injective(using BiInjective[|*|]): Injective[[x] =>> x] =
      Injective.id

  sealed trait Proper[|*|[_, _], F[_]] extends Focus[|*|, F]:
    def provePair[X]: Exists[[P] =>> Exists[[Q] =>> F[X] =:= (P |*| Q)]]

  case class Fst[|*|[_, _], F[_], B](i: Focus[|*|, F]) extends Proper[|*|, [x] =>> F[x] |*| B]:
    override def injective(using BiInjective[|*|]): Injective[[x] =>> F[x] |*| B] =
      new Injective[[x] =>> F[x] |*| B]:
        override def unapply[X, Y](ev: (F[X] |*| B) =:= (F[Y] |*| B)): Tuple1[X =:= Y] =
          ev match { case BiInjective[|*|](i.injective(ev1), _) => Tuple1(ev1) }

    override def provePair[X]: Exists[[P] =>> Exists[[Q] =>> (F[X] |*| B) =:= (P |*| Q)]] =
      Exists(Exists(summon))

  case class Snd[|*|[_, _], F[_], A](i: Focus[|*|, F]) extends Proper[|*|, [x] =>> A |*| F[x]]:
    override def injective(using BiInjective[|*|]): Injective[[x] =>> A |*| F[x]] =
      new Injective[[x] =>> A |*| F[x]]:
        override def unapply[X, Y](ev: (A |*| F[X]) =:= (A |*| F[Y])): Tuple1[X =:= Y] =
          ev match { case BiInjective[|*|](_, i.injective(ev1)) => Tuple1(ev1) }

    override def provePair[X]: Exists[[P] =>> Exists[[Q] =>> (A |*| F[X]) =:= (P |*| Q)]] =
      Exists(Exists(summon))

  def id[|*|[_, _]]: Focus[|*|, [x] =>> x] =
    Id()

  def fst[|*|[_, _], F[_], B](i: Focus[|*|, F]): Focus[|*|, [x] =>> F[x] |*| B] =
    Fst(i)

  def fst[|*|[_, _], B]: Focus[|*|, [x] =>> x |*| B] =
    fst(id[|*|])

  def snd[|*|[_, _], F[_], A](i: Focus[|*|, F]): Focus[|*|, [x] =>> A |*| F[x]] =
    Snd(i)

  def snd[|*|[_, _], A]: Focus[|*|, [x] =>> A |*| x] =
    snd(id[|*|])
}
