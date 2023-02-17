package libretto.lambda

import libretto.lambda.util.SourcePos

object UnhandledCase {
  def raise(desc: String)(using pos: SourcePos): Nothing =
      throw new UnhandledCase(desc, pos)

  private[UnhandledCase] def message(desc: String, pos: SourcePos): String =
    s"""Congratulations, you have encountered a case that no one has encountered before:
       |
       |At ${pos.filename}:${pos.line}:
       |$desc
       |
       |Please, report it at https://github.com/TomasMikula/libretto/issues/new?labels=bug
       |and, ideally, include a minimized example.
     """.stripMargin
}

class UnhandledCase(desc: String, pos: SourcePos)
extends Exception(UnhandledCase.message(desc, pos))
