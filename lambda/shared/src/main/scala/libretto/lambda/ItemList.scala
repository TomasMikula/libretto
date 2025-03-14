package libretto.lambda

@deprecated("Use Items1Named.Witness directly", since = "0.3.4")
type ItemList[||[_, _], ::[_, _], Items] =
  Items1Named.Witness[||, ::, Items]

@deprecated("Use Items1Named.Witness directly", since = "0.3.4")
transparent inline def ItemList =
  Items1Named.Witness
