package libretto.mashup.rest

import libretto.mashup.dsl.Expr

sealed trait Endpoint[I, O]

object Endpoint {
  def get[I, O](f: Expr[I] => Expr[RelativeUrl]): Endpoint[I, O] =
    ???
}
