package libretto.mashup.rest

import libretto.mashup.dsl._
import libretto.mashup.rest.RelativeUrl._

type RelativeUrl = (
  Record
    ## ("path"  of Path)
    ## ("query" of Query)
)

object RelativeUrl {
  type Path

  type Query
}
