package kindville

import scala.:: as NonEmptyList
import scala.annotation.targetName
import scala.quoted.*
import scala.util.chaining.*

private object Reporting {

  def errorAndAbort(msg: String)(using Quotes): Nothing =
    quotes.reflect.report.errorAndAbort(msg)

  def typeShortCode[T <: AnyKind](using Quotes)(t: Type[T]): String =
    typeShortCode(qr.TypeRepr.of(using t))

  def typeShortCode(using Quotes)(t: qr.TypeRepr): String =
    qr.Printer.TypeReprShortCode.show(t)

  def typeStruct(using Quotes)(t: qr.TypeRepr): String =
    qr.Printer.TypeReprStructure.show(t)

  def treeShortCode(using Quotes)(t: qr.Tree): String =
    qr.Printer.TreeShortCode.show(t)

  def treeStruct(using Quotes)(t: qr.Tree): String =
    qr.Printer.TreeStructure.show(t)

  def unsupported(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Unsupported: $msg (at $pos).\nIf you have a use case for it, please request an enhancement.")

  def unimplemented(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Unhandled case: $msg (at $pos).\n\nPlease, request an enhancement.")

  def badUse(using Quotes, Reporting.Context)(msg: String): Nothing =
    val msgInContext = msg + summon[Reporting.Context].stack.map(_.get.replace("\n", "\n  ")).mkString("\nin\n  ", "\nin\n  ", "")
    errorAndAbort(msgInContext)

  def assertionFailed(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Assertion failed: $msg (at $pos).\n\nPlease, report a bug.")

  case class Context(
    stack: NonEmptyList[LazyString], // deepest (inner-most) first
  ) {
    def push(nested: => String): Reporting.Context =
      new Context(NonEmptyList(LazyString(nested), stack))
  }

  object Context {
    def root(c: => String): Context =
      new Context(NonEmptyList(new LazyString(c), Nil))
  }

  class LazyString(value: => String) {
    lazy val get: String =
      value

    override def toString(): String =
      get
  }

  def insideMacroExpansion(using Quotes)[R](f: Reporting.Context ?=> R): R =
    insideRoot {
      quotes.reflect.Position.ofMacroExpansion.pipe: pos =>
        pos.sourceCode
          .getOrElse(s"${pos.sourceFile.name}:${pos.startLine}${if pos.endLine != pos.startLine then s"-${pos.endLine}" else ""}")
    }(f)

  def insideRoot(rootContext: => String)[R](f: Reporting.Context ?=> R): R =
    f(using Context.root(rootContext))

  @targetName("insideRootTerm")
  def insideRoot(using q: Quotes)(term: q.reflect.Term)[R](f: Reporting.Context ?=> R): R =
    insideRoot(stringify(term))(f)

  @targetName("insideRootTypeRepr")
  def insideRoot(using q: Quotes)(tpe: q.reflect.TypeRepr)[R](f: Reporting.Context ?=> R): R =
    insideRoot(stringify(tpe))(f)

  @targetName("insideRootTree")
  def insideRoot(using q: Quotes)(tree: q.reflect.Tree)[R](f: Reporting.Context ?=> R): R =
    insideRoot(stringify(tree))(f)

  def inside(using rc: Reporting.Context)(nested: => String)[R](f: Reporting.Context ?=> R): R =
    f(using rc.push(nested))

  @targetName("insideTerm")
  def inside(using q: Quotes, rc: Reporting.Context)(term: q.reflect.Term)[R](f: Reporting.Context ?=> R): R =
    inside(stringify(term))(f)

  @targetName("insideTypeRepr")
  def inside(using q: Quotes, rc: Reporting.Context)(tpe: q.reflect.TypeRepr)[R](f: Reporting.Context ?=> R): R =
    inside(stringify(tpe))(f)

  @targetName("insideTree")
  def inside(using q: Quotes, rc: Reporting.Context)(tree: q.reflect.Tree)[R](f: Reporting.Context ?=> R): R =
    inside(stringify(tree))(f)

  @targetName("stringifyTerm")
  private def stringify(using q: Quotes)(term: q.reflect.Term): String =
    term.show(using q.reflect.Printer.TreeShortCode)

  @targetName("stringifyTypeRepr")
  private def stringify(using q: Quotes)(tpe: q.reflect.TypeRepr): String =
    tpe.show(using q.reflect.Printer.TypeReprShortCode)

  @targetName("stringifyTree")
  private def stringify(using q: Quotes)(tree: q.reflect.Tree): String =
    tree.show(using q.reflect.Printer.TreeShortCode)
}
