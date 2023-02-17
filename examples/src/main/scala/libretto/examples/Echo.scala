package libretto.examples

import libretto.scaletto.StarterApp
import libretto.stream.scaletto.DefaultStreams.ValSource

/** Reads lines from standard input and prints them to standard output. */
object Echo extends StarterApp {
  override def blueprint: Done -⚬ Done =
    ValSource.repeatedly(readLine) > ValSource.forEachSequentially(printGreen)

  val printGreen: Val[String] -⚬ Done =
    mapVal[String, String](s => s"${Console.GREEN}$s${Console.RESET}") > printLine
}
