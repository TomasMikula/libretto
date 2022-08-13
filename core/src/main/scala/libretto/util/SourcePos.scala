package libretto.util

import scala.quoted._

final case class SourcePos(file: String, line: Int)

object SourcePos {
  def apply(implicit pos: SourcePos): SourcePos =
    pos

  inline implicit def sourcePosition: SourcePos =
    ${ sourcePositionImpl }

  def sourcePositionImpl(using Quotes): Expr[SourcePos] = {
    val position: quotes.reflect.Position =
      quotes.reflect.Position.ofMacroExpansion

    val file: String =
      position.sourceFile.path

    val line: Int =
      position.startLine + 1

    '{SourcePos(${Expr(file)}, ${Expr(line)})}
  }
}