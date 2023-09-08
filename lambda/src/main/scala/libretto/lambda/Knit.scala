package libretto.lambda

import libretto.lambda.util.SourcePos

sealed trait Knit[**[_, _], F[_]] {
  type Res

  def inFst[Y]: Knitted[**, [x] =>> F[x] ** Y, Res ** Y] =
    throw NotImplementedError(s"at ${summon[SourcePos]}")

  def inSnd[X]: Knitted[**, [x] =>> X ** F[x], X ** Res] =
    throw NotImplementedError(s"at ${summon[SourcePos]}")
}

object Knit {
  case class KeepFst[**[_, _], A]() extends Knit[**, [x] =>> A ** x] {
    override type Res = A
  }

  case class KeepSnd[**[_, _], B]() extends Knit[**, [x] =>> x ** B] {
    override type Res = B
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
}
