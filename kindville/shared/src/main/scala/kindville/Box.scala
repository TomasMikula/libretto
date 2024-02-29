package kindville

import scala.quoted.*

opaque type Box[As, Code <: AnyKind] = Any

object Box {
  transparent inline def pack[As, Code <: AnyKind]: Nothing => Box[As, Code] =
    ${ packImpl[As, Code] }

  transparent inline def unpack[As, Code <: AnyKind](box: Box[As, Code]): Any =
    ${ unpackImpl[As, Code]('box) }

  private def packImpl[As, Code <: AnyKind](using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Nothing => Box[As, Code]] =
    import quotes.reflect.*

    '{ (x: Any) => x }
      .asExprOf(using
        TypeRepr
          .of[Function]
          .appliedTo(
            List(
              TypeRepr.of(using decode[As, Code]),
              TypeRepr.of[Box[As, Code]],
            )
          )
          .asType
          .asInstanceOf[Type[Nothing => Box[As, Code]]]
      )

  private def unpackImpl[As, Code <: AnyKind](box: Expr[Box[As, Code]])(using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Any] =
    box.asExprOf(using decode[As, Code])

  private def decode[As, Code <: AnyKind](using
    Quotes,
    Type[As],
    Type[Code],
  ): Type[Any] =
    import quotes.reflect.*

    val args = decodeTypeArgs(Type.of[As])

    report.warning("HERE")
    TypeRepr.of[Code] match
      case outer @ TypeLambda(auxNames, auxBounds, body) =>
        val List(_) = auxNames
        val List(_) = auxBounds
        val marker = outer.param(0)
        body match
          case inner @ TypeLambda(paramNames, paramBounds, body) =>
            require(paramNames.size == args.size)
            val params = List.range(0, args.size).map(inner.param(_))
            body match
              case other => report.errorAndAbort(s"Unhandled type ${Printer.TypeReprShortCode.show(other)}")
      case other =>
        report.errorAndAbort(s"Expected a type lambda, got ${Printer.TypeReprShortCode.show(other)}")
}
