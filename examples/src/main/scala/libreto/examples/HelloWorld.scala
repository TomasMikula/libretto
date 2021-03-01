package libreto.examples

import libretto.StarterAppScala

object HelloWorld extends StarterAppScala[String] {
  override def blueprint: One -⚬ Val[String] =
    done > constVal("Hello world!")
}
