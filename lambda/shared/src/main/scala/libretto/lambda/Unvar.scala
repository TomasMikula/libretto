package libretto.lambda

import libretto.lambda.util.BiInjective

private class UnvarModule[**[_, _], V](
  varIsNotPair: [X, Y, Z] => (Var[V, X] =:= (Y ** Z)) => Nothing,
)(using
  BiInjective[**],
) {

  opaque type Unvar[VA, A] =
    StripF[**, Var[V, _], VA, A]

  object Unvar {
    def single[A]: Unvar[Var[V, A], A] =
      StripF.Single()

    def par[VA, VB, A, B](
      a: Unvar[VA, A],
      b: Unvar[VB, B],
    ): Unvar[VA ** VB, A ** B] =
      StripF.Par(a, b)

    def uniqueOutType[VA, A, B](a: Unvar[VA, A], b: Unvar[VA, B]): A =:= B =
      a.uniqueOutType(b)(varIsNotPair)

    given objectMap: SemigroupalObjectMap[**, **, Unvar] =
      StripF.objectMap(varIsNotPair)

    extension [VA, A](u: Unvar[VA, A]) {
      def from[VX](using ev: VX =:= VA): Unvar[VX, A] =
        ev.substituteContra[Unvar[_, A]](u)

      def focusFirst[R](callback: [F[_], X] => (Focus[**, F], VA =:= F[Var[V, X]]) => R): R =
        u.focusFirst(callback)
    }

    extension [A, B](u: Unvar[Var[V, A], B]) {
      def deriveEq: A =:= B =
        uniqueOutType(single[A], u)
    }
  }

}
