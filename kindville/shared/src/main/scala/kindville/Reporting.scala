package kindville

import scala.:: as NonEmptyList
import scala.annotation.targetName
import scala.quoted.*
import scala.util.chaining.*

private object Reporting {

  def errorAndAbort(msg: String)(using Quotes): Nothing =
    quotes.reflect.report.errorAndAbort(msg)

  def typeShortCode[T <: AnyKind](using Quotes, Type[T]): String =
    typeShortCode(qr.TypeRepr.of[T])

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
    val ctxStr =
      summon[Reporting.Context]
        .stack
        .map { case (reportedFrom, msg) => msg.get.replace("\n", "\n  ") + s"\n  (reported from ${reportedFrom.symbolPathLine})"}
        .mkString("in\n  ", "\nin\n  ", "")
    val msgInContext = s"$msg\n$ctxStr"
    errorAndAbort(msgInContext)

  def assertionFailed(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Assertion failed: $msg (at $pos).\n\nPlease, report a bug.")

  case class Context(
    stack: NonEmptyList[(SourcePos, LazyString)], // deepest (inner-most) first
  ) {
    def push(reportedFrom: SourcePos, nested: => String): Reporting.Context =
      new Context(NonEmptyList((reportedFrom, LazyString(nested)), stack))
  }

  object Context {
    def root(reportedFrom: SourcePos, c: => String): Context =
      new Context(NonEmptyList((reportedFrom, new LazyString(c)), Nil))
  }

  class LazyString(value: => String) {
    lazy val get: String =
      value

    override def toString(): String =
      get
  }

  def insideMacroExpansion(using q: Quotes, reportedFrom: SourcePos)[R](f: Reporting.Context ?=> R): R =
    insideRoot(reportedFrom) {
      quotes.reflect.Position.ofMacroExpansion.pipe: pos =>
        pos.sourceCode
          .getOrElse(s"${pos.sourceFile.name}:${pos.startLine}${if pos.endLine != pos.startLine then s"-${pos.endLine}" else ""}")
    }(f)

  def insideRoot(reportedFrom: SourcePos)(rootContext: => String)[R](f: Reporting.Context ?=> R): R =
    f(using Context.root(reportedFrom, rootContext))

  @targetName("insideRootTerm")
  def insideRoot(using q: Quotes, reportedFrom: SourcePos)(term: q.reflect.Term)[R](f: Reporting.Context ?=> R): R =
    insideRoot(reportedFrom)(stringify(term))(f)

  @targetName("insideRootTypeRepr")
  def insideRoot(using q: Quotes, reportedFrom: SourcePos)(tpe: q.reflect.TypeRepr)[R](f: Reporting.Context ?=> R): R =
    insideRoot(reportedFrom)(stringify(tpe))(f)

  @targetName("insideRootTree")
  def insideRoot(using q: Quotes, reportedFrom: SourcePos)(tree: q.reflect.Tree)[R](f: Reporting.Context ?=> R): R =
    insideRoot(reportedFrom)(stringify(tree))(f)

  def inside(using rc: Reporting.Context, reportedFrom: SourcePos)(nested: => String)[R](f: Reporting.Context ?=> R): R =
    f(using rc.push(reportedFrom, nested))

  @targetName("insideTerm")
  def inside(using q: Quotes, rc: Reporting.Context, reportedFrom: SourcePos)(term: q.reflect.Term)[R](f: Reporting.Context ?=> R): R =
    inside(stringify(term))(f)

  @targetName("insideTypeRepr")
  def inside(using q: Quotes, rc: Reporting.Context, reportedFrom: SourcePos)(tpe: q.reflect.TypeRepr)[R](f: Reporting.Context ?=> R): R =
    inside(stringify(tpe))(f)

  @targetName("insideTree")
  def inside(using q: Quotes, rc: Reporting.Context, reportedFrom: SourcePos)(tree: q.reflect.Tree)[R](f: Reporting.Context ?=> R): R =
    inside(stringify(tree))(f)

  def insideInlinedCall(using q: Quotes, rc: Reporting.Context, reportedFrom: SourcePos)(call: Option[q.reflect.Tree])[R](f: Reporting.Context ?=> R): R =
    call match {
      case Some(call) => inside(s"inlined call ${stringify(call)}")(f)
      case None => inside("inlined code (call unavailable)")(f)
    }

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
