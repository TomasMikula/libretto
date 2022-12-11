package libretto.lambda

sealed trait Focus[|*|[_, _], F[_]] {
  def inFst[B]: Focus[|*|, [x] =>> F[x] |*| B] =
    Focus.fst(this)

  def inSnd[A]: Focus[|*|, [x] =>> A |*| F[x]] =
    Focus.snd(this)

  def at[X]: Inj[|*|, X, F[X]] =
    Inj.focusedAt(this)
}

object Focus {
  case class Id[|*|[_, _]]() extends Focus[|*|, [x] =>> x]
  case class Fst[|*|[_, _], F[_], B](i: Focus[|*|, F]) extends Focus[|*|, [x] =>> F[x] |*| B]
  case class Snd[|*|[_, _], F[_], A](i: Focus[|*|, F]) extends Focus[|*|, [x] =>> A |*| F[x]]

  def id[|*|[_, _]]: Focus[|*|, [x] =>> x] =
    Id()

  def fst[|*|[_, _], F[_], B](i: Focus[|*|, F]): Focus[|*|, [x] =>> F[x] |*| B] =
    Fst(i)

  def snd[|*|[_, _], F[_], A](i: Focus[|*|, F]): Focus[|*|, [x] =>> A |*| F[x]] =
    Snd(i)
}
