package kindville

import scala.annotation.tailrec
import scala.quoted.*

private[kindville] final case class SourcePos(path: String, filename: String, line: Int, insideSymbol: String) {
  override def toString: String =
    s"$path:$line"

  def symbolPathLine: String =
    s"$insideSymbol ($path:$line)"
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

    val ownerSymbol =
      quotes.reflect.Symbol.spliceOwner

    val ownerName =
      ownerOfInterest(ownerSymbol).fullName

    '{SourcePos(${Expr(path)}, ${Expr(filename)}, ${Expr(line)}, ${Expr(ownerName)})}
  }

  private def ownerOfInterest(using q: Quotes)(symbol: q.reflect.Symbol): q.reflect.Symbol =
    @tailrec
    def go(symbol: q.reflect.Symbol): q.reflect.Symbol =
      if (symbol.isClassDef || (symbol.isDefDef && !symbol.isAnonymousFunction) || symbol.isPackageDef || symbol.isNoSymbol)
        symbol
      else
        go(symbol.owner)

    val s = go(symbol)
    if (s.isNoSymbol) then symbol else s

}
