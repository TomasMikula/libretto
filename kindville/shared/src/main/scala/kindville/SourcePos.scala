package kindville

import scala.quoted.*

private[kindville] final case class SourcePos(path: String, filename: String, line: Int) {
  override def toString: String =
    s"$path:$line"
}

private[kindville] object SourcePos {
  def apply(using pos: SourcePos): SourcePos =
    pos

  inline given SourcePos =
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
