package libretto.examples

import libretto.scaletto.StarterAppScala

object HelloWorld extends StarterAppScala[String] {
  override def blueprint: Done -⚬ Val[String] =
    constVal("Hello world!")
}
