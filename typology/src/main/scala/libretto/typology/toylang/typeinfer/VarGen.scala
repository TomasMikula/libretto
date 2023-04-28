package libretto.typology.toylang.typeinfer

trait VarGen[M[_], V] {
  def newVar: M[V]
}
