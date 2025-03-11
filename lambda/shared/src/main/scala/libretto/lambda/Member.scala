package libretto.lambda

@deprecated("Use Items1Named.Member directly", since = "0.3.4")
type Member[||[_, _], ::[_, _], Label, A, Cases] =
  Items1Named.Member[||, ::, Label, A, Cases]

@deprecated("Use Items1Named.Member directly", since = "0.3.4")
transparent inline def Member =
  Items1Named.Member
