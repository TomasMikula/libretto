package libretto.lambda.util

import scala.quoted._

final case class SourcePos(path: String, filename: String, line: Int)

object SourcePos {
  def apply(implicit pos: SourcePos): SourcePos =
    pos

  inline implicit def sourcePosition: SourcePos =
    ${ sourcePositionImpl }

  def sourcePositionImpl(using Quotes): Expr[SourcePos] = {
    val position: quotes.reflect.Position =
      quotes.reflect.Position.ofMacroExpansion

    val path: String =
      position.sourceFile.path

    val filename: String =
      position.sourceFile.name

    val line: Int =
      position.startLine + 1

    '{SourcePos(${Expr(path)}, ${Expr(filename)}, ${Expr(line)})}
  }
}