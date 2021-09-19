package libretto.impl

sealed trait VarOrigin

object VarOrigin {
  case class FunApp(file: String, line: Int) extends VarOrigin
  case class Pairing(file: String, line: Int) extends VarOrigin
  case class Prj1(file: String, line: Int) extends VarOrigin
  case class Prj2(file: String, line: Int) extends VarOrigin
  case class Lambda(file: String, line: Int) extends VarOrigin
  case class ClosureVal(file: String, line: Int) extends VarOrigin
}
