package libretto.scaletto.impl

import libretto.util.SourcePos

sealed trait VarOrigin {
  import VarOrigin._

  def print: String =
    this match {
      case FunApp(SourcePos(f, l))     => s"The result of function application at $f:$l"
      case Pairing(SourcePos(f, l))    => s"The pair created at $f:$l"
      case Prj1(SourcePos(f, l))       => s"The first half of untupling at $f:$l"
      case Prj2(SourcePos(f, l))       => s"The second half of untupling at $f:$l"
      case Lambda(SourcePos(f, l))     => s"The input of lambda expression ending at $f:$l"
      case ClosureVal(SourcePos(f, l)) => s"The value of closure expression at $f:$l"
      case OneIntro(SourcePos(f, l))   => s"The unit introduced at $f:$l"
      case Synthetic(desc)            => s"Synthetic variable: $desc"
    }
}

object VarOrigin {
  case class FunApp(pos: SourcePos) extends VarOrigin
  case class Pairing(pos: SourcePos) extends VarOrigin
  case class Prj1(pos: SourcePos) extends VarOrigin
  case class Prj2(pos: SourcePos) extends VarOrigin
  case class Lambda(pos: SourcePos) extends VarOrigin
  case class ClosureVal(pos: SourcePos) extends VarOrigin
  case class OneIntro(pos: SourcePos) extends VarOrigin
  case class Synthetic(description: String) extends VarOrigin
}
