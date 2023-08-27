package libretto.lambda

sealed trait Capture[**[_, _], F[_], A, B]

object Capture {
  case class NoCapture[**[_, _], F[_], A]() extends Capture[**, F, A, A]
  sealed trait Proper[**[_, _], F[_], A, B] extends Capture[**, F, A, B]
  case class CaptureFst[**[_, _], F[_], A, B1, B2](b1: Tupled[**, F, B1], f: Capture[**, F, A, B2]) extends Proper[**, F, A, B1 ** B2]
  case class CaptureSnd[**[_, _], F[_], A, B1, B2](f: Capture[**, F, A, B1], b2: Tupled[**, F, B2]) extends Proper[**, F, A, B1 ** B2]
  case class Par[**[_, _], F[_], A1, A2, B1, B2](f1: Proper[**, F, A1, B1], f2: Proper[**, F, A2, B2]) extends Proper[**, F, A1 ** A2, B1 ** B2]
}
