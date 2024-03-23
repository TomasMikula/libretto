package kindville

import scala.quoted.*

object Box {
  transparent inline def packer[Code <: AnyKind]: Any =
    ${ packerImpl[Code] }

  transparent inline def pack[As, Code <: AnyKind]: Nothing => Box[As, Code] =
    ${ packImpl[As, Code] }

  transparent inline def unpack[As, Code <: AnyKind](box: Box[As, Code]): Any =
    ${ unpackImpl[As, Code]('box) }

  private def packerImpl[Code <: AnyKind](using
    Quotes,
    Type[Code],
  ): Expr[Any] =
    import quotes.reflect.*

    val encoding = Encoding()
    import encoding.{TypeLambdaTemplate, decodeTypeLambda}
    val TypeLambdaTemplate(names, bounds, body) = decodeTypeLambda[Code]

    def returnType(targs: List[TypeRepr]): TypeRepr =
      TypeRepr
        .of[Box]
        .appliedTo(
          Encoding.encodeTypeArgs(targs) ::
          TypeRepr.of[Code] ::
          Nil
        )

    PolyFun(
      names,
      bounds,
      "x" :: Nil,
      tparams => body(tparams) :: Nil,
      tparams => returnType(tparams),
      (targs, args, owner) => {
        returnType(targs).asType match
          case '[t] =>
            '{ ${args(0).asExpr}.asInstanceOf[t] }.asTerm
      },
    ).asExpr

  private def packImpl[As, Code <: AnyKind](using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Nothing => Box[As, Code]] =
    import quotes.reflect.*

    Encoding().decodeType[As, Code] match
      case '[t] =>
        '{ (x: t) => x.asInstanceOf[Box[As, Code]] }

  private def unpackImpl[As, Code <: AnyKind](box: Expr[Box[As, Code]])(using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Any] =
    Encoding().decodeType[As, Code] match
      case '[t] => '{ $box.asInstanceOf[t] }
}
