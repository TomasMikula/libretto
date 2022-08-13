package libretto.examples

import libretto.scaletto.StarterApp

/** Reads lines from standard input and prints them to standard output. */
object Echo extends StarterApp {
  override def blueprint: Done -⚬ Done =
    Pollable.repeatedly(readLine) > Pollable.forEachSequentially(printGreen)

  val printGreen: Val[String] -⚬ Done =
    mapVal[String, String](s => s"${Console.GREEN}$s${Console.RESET}") > printLine
}
