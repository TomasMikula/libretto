package libretto.util.atomic

import java.util.concurrent.atomic.AtomicReference
import scala.annotation.tailrec

extension [A <: AnyRef](ref: AtomicReference[A]) {
  def modifyOpaque[C](f: A => (A, C)): C = {
    @tailrec def go(expected: A): C = {
      val res: (A, C) = f(expected)
      val changed: A = compareAndSetOpaque[A](ref, expected, res._1)
      if (changed eq res._1)
        res._2
      else
        go(changed)
    }

    go(ref.getOpaque())
  }

  def modifyOpaqueWith[B, C](b: B, f: (A, B) => (A, C)): C = {
    @tailrec def go(expected: A): C = {
      val res: (A, C) = f(expected, b)
      val changed: A = compareAndSetOpaque[A](ref, expected, res._1)
      if (changed eq res._1) // success
        res._2
      else
        go(changed)
    }

    go(ref.getOpaque())
  }
}

/** Returns the value of `ref` afterwards.
  * If it is `next`, it means the operation was successful. Otherwise, the value has changed.
  */
@tailrec private def compareAndSetOpaque[A <: AnyRef](
  ref: AtomicReference[A],
  expected: A,
  next: A,
): A = {
  if (ref.weakCompareAndSetPlain(expected, next)) {
    next // success
  } else {
    val current = ref.getOpaque()
    if (current eq expected)
      compareAndSetOpaque(ref, expected, next)
    else
      current
  }
}
