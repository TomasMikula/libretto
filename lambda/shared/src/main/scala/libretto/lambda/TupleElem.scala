package libretto.lambda

@deprecated("Use Items1.Member directly", since = "0.3.4")
type TupleElem[||[_, _], Nil, A, As] =
  Items1.Member[||, Nil, A, As]

@deprecated("Use Items1.Member directly", since = "0.3.4")
transparent inline def TupleElem =
  Items1.Member
