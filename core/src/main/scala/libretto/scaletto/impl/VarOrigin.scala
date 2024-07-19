package libretto.scaletto.impl

import libretto.lambda.util.SourcePos

sealed trait VarOrigin {
  import VarOrigin.*

  def print: String =
    this match {
      case FunAppRes(SourcePos(p, _, l))    => s"The result of function application at $p:$l"
      case ExtractorRes(SourcePos(p, _, l)) => s"The result of extractor at $p:$l"
      case FunAndArg(SourcePos(p, _, l))    => s"The pair of function and its argument at $p:$l"
      case Pairing(SourcePos(p, _, l))      => s"The pair created at $p:$l"
      case Prj1(SourcePos(p, _, l))         => s"The first half of untupling at $p:$l"
      case Prj2(SourcePos(p, _, l))         => s"The second half of untupling at $p:$l"
      case Lambda(SourcePos(p, _, l))       => s"The variable bound by lambda expression at $p:$l"
      case CapturedVars(SourcePos(p, _, l)) => s"Aggregate of captured expressions at $p:$l"
      case ClosureVal(SourcePos(p, _, l))   => s"The value of closure expression at $p:$l"
      case SwitchIn(SourcePos(p, _, l))     => s"The input to switch at $p:$l (the scrutinee paired with any captured expressions)"
      case SwitchCase(SourcePos(p, _, l))   => s"The input to switch case at $p:$l"
      case SwitchOut(SourcePos(p, _, l))    => s"The result of switch expression at $p:$l"
      case OneIntro(SourcePos(p, _, l))     => s"The unit introduced at $p:$l"
      case NonLinearOps(SourcePos(p, _, l)) => s"The variable equipped with non-linear ops at $p:$l"
      case CapturedVarsAndFunArg(SourcePos(p, _, l)) => s"Aggregate of captured expressions and function argument at $p:$l"
    }
}

object VarOrigin {
  case class FunAppRes(pos: SourcePos) extends VarOrigin
  case class ExtractorRes(pos: SourcePos) extends VarOrigin
  case class FunAndArg(pos: SourcePos) extends VarOrigin
  case class Pairing(pos: SourcePos) extends VarOrigin
  case class Prj1(pos: SourcePos) extends VarOrigin
  case class Prj2(pos: SourcePos) extends VarOrigin
  case class Lambda(pos: SourcePos) extends VarOrigin
  case class CapturedVars(pos: SourcePos) extends VarOrigin
  case class CapturedVarsAndFunArg(pos: SourcePos) extends VarOrigin
  case class ClosureVal(pos: SourcePos) extends VarOrigin
  case class SwitchIn(pos: SourcePos) extends VarOrigin
  case class SwitchCase(pos: SourcePos) extends VarOrigin
  case class SwitchOut(pos: SourcePos) extends VarOrigin
  case class OneIntro(pos: SourcePos) extends VarOrigin
  case class NonLinearOps(pos: SourcePos) extends VarOrigin
}
