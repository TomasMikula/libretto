package kindville

import scala.quoted.*

sealed trait *
sealed trait ->[K, L]

sealed trait ::[H <: AnyKind, T]
sealed trait TNil

sealed trait ofKind[F <: AnyKind, K]
sealed trait ofKinds[As, Ks]

extension [FA](fa: FA)
  transparent inline def unmask[F <: AnyKind, As](using ev: TypeApp[F, As, FA]): Any =
    ${ unmaskImpl('fa, 'ev) }

private[kindville] def unmaskImpl[F <: AnyKind, As, FA](
  fa: Expr[FA],
  ev: Expr[TypeApp[F, As, FA]],
)(using
  Quotes,
  Type[F],
  Type[As],
//   Type[FA],
): Expr[Any] =
  import quotes.reflect.*
  val targs: List[Type[?]] = decodeTypeArgs[As](Type.of[As])
  Expr(Printer.TypeReprCode.show(TypeRepr.of[As]))
  cast(fa, Type.of[F], targs)

private[kindville] def encodeTypeArgs(using Quotes)(args: List[quotes.reflect.TypeRepr]): quotes.reflect.TypeRepr =
  import quotes.reflect.*
  args match
    case Nil => TypeRepr.of[TNil]
    case t :: ts => TypeRepr.of[::].appliedTo(List(t, encodeTypeArgs(ts)))

private[kindville] def decodeTypeArgs[As <: AnyKind](args: Type[As])(using Quotes): List[Type[?]] =
  import quotes.reflect.*

  val cons = TypeRepr.of[::]

  args match
    case '[TNil] => Nil
    case other =>
      val repr = TypeRepr.of(using other)
      repr match
        case AppliedType(f, args) =>
          f.asType match
            case '[::] =>
              args match
                case h :: t :: Nil =>
                  h.asType :: decodeTypeArgs(t.asType)(using quotes)
                case _ =>
                  report.errorAndAbort(s"Unexpected number of type arguments to ${Printer.TypeReprShortCode.show(f)}. Expected 2, got ${args.size}: ${args.map(Printer.TypeReprShortCode.show(_).mkString(", "))}")
            case other =>
              report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
              Nil
        case other =>
          report.error(s"Cannot decode a list of type arguments from type ${Printer.TypeReprShortCode.show(repr)}")
          Nil

private[kindville] def cast[FA, F <: AnyKind](
  expr: Expr[FA],
  tf: Type[F],
  targs: List[Type[?]],
)(using Quotes): Expr[Any] =
  import quotes.reflect.*

  val resultType: Type[?] =
    TypeRepr.of(using tf)
      .appliedTo(targs.map(TypeRepr.of(using _)))
      .asType

  expr.asExprOf(using resultType.asInstanceOf[Type[Any]])