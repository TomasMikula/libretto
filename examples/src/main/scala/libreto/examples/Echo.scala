package libreto.examples

import libretto.StarterApp

/** Reads lines from standard input and prints them to standard output. */
object Echo extends StarterApp {
  override def blueprint: One -⚬ Done =
    done > Pollable.repeatedly(readLine) > Pollable.forEachSequentially(printGreen)

  val printGreen: Val[String] -⚬ Done =
    mapVal[String, String](s => s"${Console.GREEN}$s${Console.RESET}") > printLine
}
