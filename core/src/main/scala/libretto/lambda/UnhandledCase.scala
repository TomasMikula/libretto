package libretto.lambda

object UnhandledCase {
  def raise(desc: String): Nothing =
      throw new UnhandledCase(desc)

  private[UnhandledCase] def message(desc: String): String =
    s"""Congratulations, you have encountered a case that no one has encountered before:
       |
       |$desc
       |
       |Please, report it at https://github.com/TomasMikula/libretto/issues/new?labels=bug
       |and include a minimized example.
     """.stripMargin
}

class UnhandledCase(desc: String) extends Exception(UnhandledCase.message(desc))
