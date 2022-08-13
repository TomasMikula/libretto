package libretto.lambda

import libretto.util.UniqueTypeArg

trait Variable[Var[_], VarSet] extends UniqueTypeArg[Var] {
  def singleton[A](v: Var[A]): VarSet
  def union(vs: VarSet, ws: VarSet): VarSet
}
