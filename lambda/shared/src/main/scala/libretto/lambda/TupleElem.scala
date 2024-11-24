package libretto.lambda

import libretto.lambda.util.Exists

/**
  * Witnesses that `A` is one of `As`,
  * where `As` is of the form `Nil || A1 || A2 || ...`
  * (where `||` associates to the left).
  *
  * Unlike [[Member]], `TupleElem` is for *unnamed* tuples.
  */
sealed trait TupleElem[||[_, _], Nil, A, As] {
  def inInit[B]: TupleElem[||, Nil, A, As || B] =
    TupleElem.InInit(this)

  def ownerTypeAsTuple[R](f: [X, Y] => (As =:= (X || Y)) ?=> R): R

  def ownerTypeIsTuple: Exists[[X] =>> Exists[[Y] =>> As =:= (X || Y)]] =
    ownerTypeAsTuple([X, Y] => (_) ?=> Exists(Exists(summon)))
}

object TupleElem {
  case class Last[||[_, _], Nil, Init, Z]() extends TupleElem[||, Nil, Z, Init || Z] {
    override def ownerTypeAsTuple[R](f: [X, Y] => ((Init || Z) =:= (X || Y)) ?=> R): R =
      f[Init, Z]
  }

  case class InInit[||[_, _], Nil, A, Init, Z](
    init: TupleElem[||, Nil, A, Init],
  ) extends TupleElem[||, Nil, A, Init || Z] {
    override def ownerTypeAsTuple[R](f: [X, Y] => ((Init || Z) =:= (X || Y)) ?=> R): R =
      f[Init, Z]
  }

  def single[||[_, _], Nil, A]: TupleElem[||, Nil, A, Nil || A] =
    Last()
}
