package libretto.typology.toylang

import libretto.typology.kinds._

package object types {
  type Type[V] = TypeExpr[V, ○, ●]

  /** Used as a phantom type representing a reference to a surrounding recursive function. */
  sealed trait RecCall[A, B]
}
