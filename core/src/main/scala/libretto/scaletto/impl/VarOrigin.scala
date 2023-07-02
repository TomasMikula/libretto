package libretto.scaletto.impl

import libretto.lambda.util.SourcePos

sealed trait VarOrigin {
  import VarOrigin.*

  def print: String =
    this match {
      case FunAppRes(SourcePos(p, _, l))    => s"The result of function application at $p:$l"
      case FunAndArg(SourcePos(p, _, l))    => s"The pair of function and its argument at $p:$l"
      case Pairing(SourcePos(p, _, l))      => s"The pair created at $p:$l"
      case Prj1(SourcePos(p, _, l))         => s"The first half of untupling at $p:$l"
      case Prj2(SourcePos(p, _, l))         => s"The second half of untupling at $p:$l"
      case Lambda(SourcePos(p, _, l))       => s"The variable bound by lambda expression at $p:$l"
      case ClosureVal(SourcePos(p, _, l))   => s"The value of closure expression at $p:$l"
      case OneIntro(SourcePos(p, _, l))     => s"The unit introduced at $p:$l"
      case NonLinearOps(SourcePos(p, _, l)) => s"The variable equipped with non-linear ops at $p:$l"
      case Synthetic(desc)                  => s"Synthetic variable: $desc"
    }
}

object VarOrigin {
  case class FunAppRes(pos: SourcePos) extends VarOrigin
  case class FunAndArg(pos: SourcePos) extends VarOrigin
  case class Pairing(pos: SourcePos) extends VarOrigin
  case class Prj1(pos: SourcePos) extends VarOrigin
  case class Prj2(pos: SourcePos) extends VarOrigin
  case class Lambda(pos: SourcePos) extends VarOrigin
  case class ClosureVal(pos: SourcePos) extends VarOrigin
  case class OneIntro(pos: SourcePos) extends VarOrigin
  case class NonLinearOps(pos: SourcePos) extends VarOrigin
  case class Synthetic(description: String) extends VarOrigin
}
