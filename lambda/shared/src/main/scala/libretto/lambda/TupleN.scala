package libretto.lambda

@deprecated("Use Items1.Product directly", since = "0.3.4")
type TupleN[∙[_, _], Nil, F[_], A] =
  Items1.Product[∙, Nil, F, A]

@deprecated("Use Items1.Product directly", since = "0.3.4")
transparent inline def TupleN =
  Items1.Product
