package kindville

import scala.quoted.*

object Box {
  transparent inline def packer[Code[⋅⋅[_]] <: AnyKind]: Any =
    ${ packerImpl[Code] }

  transparent inline def unpacker[Code[⋅⋅[_]] <: AnyKind]: Any =
    ${ unpackerImpl[Code] }

  transparent inline def pack[Code[⋅⋅[_]] <: AnyKind, As]: Nothing => Box[Code, As] =
    ${ packImpl[Code, As] }

  transparent inline def pacK[K, Code[⋅⋅[_]] <: AnyKind, As]: Any =
    decodeCompositeExpr[[⋅⋅[_]] =>> Code[⋅⋅] :: As :: TNil](
      [⋅⋅[_], Code0[As <: ⋅⋅[K]], A0 <: ⋅⋅[K]] =>
        (packer: [X <: ⋅⋅[K]] => Code0[X] => Box[Code, ⋅⋅[X]]) =>
          packer[A0]
    )(
      packer[Code],
    )

  transparent inline def unpack[Code[⋅⋅[_]] <: AnyKind, As](box: Box[Code, As]): Any =
    ${ unpackImpl[Code, As]('box) }

  private def boxType(using Quotes)(
    code: qr.TypeRepr,
    args: List[qr.TypeRepr],
  ): qr.TypeRepr =
    qr.TypeRepr
      .of[Box]
      .appliedTo(
        code ::
        Encoding.encodeTypeArgs(args) ::
        Nil
      )

  private def packerImpl[Code <: AnyKind](using
    Quotes,
    Type[Code],
  ): Expr[Any] =
    import quotes.reflect.*

    val encoding = Encoding()
    import encoding.{TypeLambdaTemplate, decodeTypeLambda}
    val TypeLambdaTemplate(names, bounds, body) = decodeTypeLambda[Code]

    def returnType(targs: List[TypeRepr]): TypeRepr =
      boxType(TypeRepr.of[Code], targs)

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

  private def unpackerImpl[Code <: AnyKind](using
    Quotes,
    Type[Code],
  ): Expr[Any] =
    import quotes.reflect.*

    val encoding = Encoding()
    import encoding.{TypeLambdaTemplate, decodeTypeLambda}
    val TypeLambdaTemplate(names, bounds, body) = decodeTypeLambda[Code]

    def paramType(targs: List[TypeRepr]): TypeRepr =
      boxType(TypeRepr.of[Code], targs)

    PolyFun(
      names,
      bounds,
      "x" :: Nil,
      tparams => paramType(tparams) :: Nil,
      tparams => body(tparams),
      (targs, args, owner) => {
        body(targs).asType match
          case '[t] =>
            '{ ${args(0).asExpr}.asInstanceOf[t] }.asTerm
      },
    ).asExpr

  private def packImpl[Code[⋅⋅[_]] <: AnyKind, As](using
    Quotes,
    Type[Code],
    Type[As],
  ): Expr[Nothing => Box[Code, As]] =
    import quotes.reflect.*

    Encoding().decodeParameterizedType[Code, As] match
      case '[t] =>
        '{ (x: t) => x.asInstanceOf[Box[Code, As]] }

  private def unpackImpl[Code[⋅⋅[_]] <: AnyKind, As](box: Expr[Box[Code, As]])(using
    Quotes,
    Type[Code],
    Type[As],
  ): Expr[Any] =
    Encoding().decodeParameterizedType[Code, As] match
      case '[t] => '{ $box.asInstanceOf[t] }
}
