package libretto.util

import java.util.concurrent.atomic.AtomicReference
import scala.annotation.tailrec

package object atomic {
  private inline val Debug = false

  private inline def debugPrint(s: String): Unit =
    if (Debug) println(s)

  private def addr[X](c: AtomicReference[X]): String =
    "@" + System.identityHashCode(c).toHexString

  extension [A <: AnyRef](ref: AtomicReference[A]) {
    def modifyOpaque[C](f: A => (A, C)): C = {
      @tailrec def go(expected: A): C = {
        val res: (A, C) = f(expected)
        val changed: A = compareAndSetOpaque[A](ref, expected, res._1)
        if (changed eq res._1) // success
          debugPrint(s"${addr(ref)} set to $changed, returning ${res._2}")
          res._2
        else
          go(changed)
      }

      go(ref.getOpaque())
    }

    def modifyOpaqueOpt[C](f: A => (Option[A], C)): C = {
      @tailrec def go(expected: A): C = {
        val res: (Option[A], C) = f(expected)
        res._1 match {
          case None =>
            debugPrint(s"${addr(ref)} unchanged by $f, remaining at $expected, returning ${res._2}")
            res._2
          case Some(a) =>
            val changed: A = compareAndSetOpaque[A](ref, expected, a)
            if(changed eq a) // success
              debugPrint(s"${addr(ref)} set to $changed, returning ${res._2}")
              res._2
            else
              go(changed)
        }
      }

      go(ref.getOpaque())
    }

    def modifyOpaqueWith[B, C](b: B, f: (A, B) => (A, C)): C = {
      @tailrec def go(expected: A): C = {
        val res: (A, C) = f(expected, b)
        val changed: A = compareAndSetOpaque[A](ref, expected, res._1)
        if (changed eq res._1) // success
          debugPrint(s"${addr(ref)} set to $changed, returning ${res._2}")
          res._2
        else
          go(changed)
      }

      go(ref.getOpaque())
    }

    def modifyOpaqueOptWith[B, C](b: B, f: (A, B) => (Option[A], C)): C = {
      @tailrec def go(expected: A): C = {
        val res: (Option[A], C) = f(expected, b)
        res._1 match {
          case None =>
            debugPrint(s"${addr(ref)} unchanged by $b, remaining at $expected, returning ${res._2}")
            res._2
          case Some(a) =>
            val changed: A = compareAndSetOpaque[A](ref, expected, a)
            if (changed eq a) // success
              debugPrint(s"${addr(ref)} set to $changed, returning ${res._2}")
              res._2
            else
              go(changed)
        }
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
}
