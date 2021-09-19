package libretto.impl

trait Variable[Var[_], VarSet] extends Unique[Var] {
  def singleton[A](v: Var[A]): VarSet
  def union(vs: VarSet, ws: VarSet): VarSet
}
