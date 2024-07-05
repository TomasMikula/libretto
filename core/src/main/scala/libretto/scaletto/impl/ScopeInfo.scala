package libretto.scaletto.impl

import libretto.lambda.util.SourcePos

enum ScopeInfo {
  case TopLevelLambda(pos: SourcePos)
  case NestedLambda(pos: SourcePos)
  case SwitchCase(casePos: SourcePos)
  case ValCase(casePos: SourcePos)

  def print: String =
    this match
      case TopLevelLambda(pos) => s"lambda at ${pos.filename}:${pos.line}"
      case NestedLambda(pos) => s"nested lambda (closure) at ${pos.filename}:${pos.line}"
      case SwitchCase(casePos) => s"switch case at ${casePos.filename}:${casePos.line}"
      case ValCase(casePos) => s"Val case at ${casePos.filename}:${casePos.line}"

  def sourcePos: SourcePos =
    this match
      case TopLevelLambda(pos) => pos
      case NestedLambda(pos) => pos
      case SwitchCase(casePos) => casePos
      case ValCase(casePos) => casePos

  override def toString: String =
    print
}
