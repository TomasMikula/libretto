package libretto.lambda.util

import scala.quoted.*

object unapply {
  trait Unapply[FA, F[_]] {
    type A
    def ev: FA =:= F[A]
  }

  object Unapply {
    def apply[F[_], X]: Unapply[F[X], F] { type A = X } = new Unapply[F[X], F] {
      type A = X
      val ev: F[X] =:= F[A] = summon
    }

    private def forced[FX, F[_], X]: Unapply[FX, F] { type A = X } =
      new Unapply[FX, F] {
        override type A = X
        override def ev: FX =:= F[X] = summon[FX =:= FX].asInstanceOf[FX =:= F[X]]
      }

    given [F[_], X]: Unapply[F[X], F] { type A = X } =
      apply[F, X]

    transparent inline given derive[FX, F[_]]: Unapply[FX, F] =
      ${ unapplyImpl[FX, F] }

    private def unapplyImpl[FX, F[_]](using Quotes, Type[FX], Type[F]): Expr[Unapply[FX, F]] =
      import quotes.reflect.{Unapply => _, *}

      Type.of[FX] match
        case '[F[x]] =>
          '{ Unapply[F, x] }.asExprOf[Unapply[FX, F] { type A = x }]
        case _ =>
          TypeRepr.of[FX].dealiasKeepOpaques match
            case AppliedType(f, List(x)) if f =:= TypeRepr.of[F] =>
              x.asType match
                case '[x] => '{ forced[FX, F, x] }
            case other =>
              report.errorAndAbort(s"Cannot prove that ${TypeRepr.of[FX].show} or ${other.show} is an application of ${TypeRepr.of[F].show}")
  }

  trait Unapply2[FAB, F[_, _]] {
    type A
    type B
    def ev: FAB =:= F[A, B]
  }

  object Unapply2 {
    given [F[_, _], X, Y]: Unapply2[F[X, Y], F] with {
      type A = X
      type B = Y
      val ev: F[X, Y] =:= F[A, B] = summon
    }
  }
}
