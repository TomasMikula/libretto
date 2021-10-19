package libretto.impl

sealed trait VarOrigin {
  import VarOrigin._

  def print: String =
    this match {
      case FunApp(f, l)     => s"Result of function application at $f:$l"
      case Pairing(f, l)    => s"Pair created at $f:$l"
      case Prj1(f, l)       => s"First half of untupling at $f:$l"
      case Prj2(f, l)       => s"Second half of untupling at $f:$l"
      case Lambda(f, l)     => s"Introduced by lambda expression ending at $f:$l"
      case ClosureVal(f, l) => s"Value of closure expression at $f:$l"
    }
}

object VarOrigin {
  case class FunApp(file: String, line: Int) extends VarOrigin
  case class Pairing(file: String, line: Int) extends VarOrigin
  case class Prj1(file: String, line: Int) extends VarOrigin
  case class Prj2(file: String, line: Int) extends VarOrigin
  case class Lambda(file: String, line: Int) extends VarOrigin
  case class ClosureVal(file: String, line: Int) extends VarOrigin
}
