package libretto.impl

import libretto.scalasource.Position

sealed trait VarOrigin {
  import VarOrigin._

  def print: String =
    this match {
      case FunApp(Position(f, l))     => s"The result of function application at $f:$l"
      case Pairing(Position(f, l))    => s"The pair created at $f:$l"
      case Prj1(Position(f, l))       => s"The first half of untupling at $f:$l"
      case Prj2(Position(f, l))       => s"The second half of untupling at $f:$l"
      case Lambda(Position(f, l))     => s"The input of lambda expression ending at $f:$l"
      case ClosureVal(Position(f, l)) => s"The value of closure expression at $f:$l"
      case OneIntro(Position(f, l))   => s"The unit introduced at $f:$l"
      case Synthetic(desc)            => s"Synthetic variable: $desc"
    }
}

object VarOrigin {
  case class FunApp(pos: Position) extends VarOrigin
  case class Pairing(pos: Position) extends VarOrigin
  case class Prj1(pos: Position) extends VarOrigin
  case class Prj2(pos: Position) extends VarOrigin
  case class Lambda(pos: Position) extends VarOrigin
  case class ClosureVal(pos: Position) extends VarOrigin
  case class OneIntro(pos: Position) extends VarOrigin
  case class Synthetic(description: String) extends VarOrigin
}
