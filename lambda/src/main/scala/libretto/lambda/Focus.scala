package libretto.lambda

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
}

object Focus {
  case class Id[|*|[_, _]]() extends Focus[|*|, [x] =>> x]
  case class Fst[|*|[_, _], F[_], B](i: Focus[|*|, F]) extends Focus[|*|, [x] =>> F[x] |*| B]
  case class Snd[|*|[_, _], F[_], A](i: Focus[|*|, F]) extends Focus[|*|, [x] =>> A |*| F[x]]

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
