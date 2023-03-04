package libretto.scaletto.impl

import libretto.util.Async

enum ScalaFunction[A, B] {
  case Direct(f: A => B)
  case Blocking(f: A => B)
  case Asynchronous(f: A => Async[B])
}
