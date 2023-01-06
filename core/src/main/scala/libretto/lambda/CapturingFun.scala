package libretto.lambda


sealed trait CapturingFun[-->[_, _], |*|[_, _], F[_], A, B] {

}

object CapturingFun {
  case class NoCapture[-->[_, _], |*|[_, _], F[_], A, B](f: A --> B) extends CapturingFun[-->, |*|, F, A, B]
  case class Closure[-->[_, _], |*|[_, _], F[_], X, A, B](captured: F[X], f: (X |*| A) --> B) extends CapturingFun[-->, |*|, F, A, B]
}
