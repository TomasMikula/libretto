package kindville

import scala.quoted.*

private object Reporting {

  // TODO: use report.errorAndAbort after https://github.com/lampepfl/dotty/issues/19851 is fixed
  def errorAndAbort(msg: String)(using Quotes): Nothing =
    quotes.reflect.report.error(msg)
    ???

  def typeShortCode[T <: AnyKind](using Quotes)(t: Type[T]): String =
    typeShortCode(qr.TypeRepr.of(using t))

  def typeShortCode(using Quotes)(t: qr.TypeRepr): String =
    qr.Printer.TypeReprShortCode.show(t)

  def treeShortCode(using Quotes)(t: qr.Tree): String =
    qr.Printer.TreeShortCode.show(t)

  def treeStruct(using Quotes)(t: qr.Tree): String =
    qr.Printer.TreeStructure.show(t)

  def unsupported(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Unsupported: $msg (at $pos).\nIf you have a use case for it, please request an enhancement.")

  def unimplemented(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Unhandled case: $msg (at $pos).\n\nPlease, request an enhancement.")

  def badUse(using Quotes)(msg: String): Nothing =
    errorAndAbort(msg)

  def assertionFailed(using pos: SourcePos, q: Quotes)(msg: String): Nothing =
    errorAndAbort(s"Assertion failed: $msg (at $pos).\n\nPlease, report a bug.")
}
