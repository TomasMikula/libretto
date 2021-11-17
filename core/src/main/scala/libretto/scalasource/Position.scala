package libretto.scalasource

import scala.quoted._

final case class Position(file: String, line: Int)

object Position {
  def apply(implicit pos: Position): Position =
    pos

  inline implicit def sourcePosition: Position =
    ${ sourcePositionImpl }

  def sourcePositionImpl(using Quotes): Expr[Position] = {
    val position: quotes.reflect.Position =
      quotes.reflect.Position.ofMacroExpansion

    val file: String =
      position.sourceFile.path

    val line: Int =
      position.startLine + 1

    '{Position(${Expr(file)}, ${Expr(line)})}
  }
}