package libretto

/** Used to document laws in a typechecked manner. The purpose of expression `Equal(f, g)` is just to ensure
  * that `f` and `g` compile and are of the same type.
  */
case class Equal[A](a1: A, a2: A)
