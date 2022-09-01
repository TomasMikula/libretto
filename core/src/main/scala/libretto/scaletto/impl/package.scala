package libretto.scaletto

package object impl {
  def bug[A](msg: String): A =
    throw new AssertionError(
      s"""$msg
          |This is a bug, please report at https://github.com/TomasMikula/libretto/issues/new?labels=bug"""
        .stripMargin
    )
}
