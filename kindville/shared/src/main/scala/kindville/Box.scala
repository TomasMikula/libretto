package kindville

import kindville.Reporting.{inside, insideMacroExpansion}
import scala.quoted.*

object Box {
  transparent inline def packer[Code[⋅⋅[_]] <: AnyKind]: Any =
    ${ packerImpl[Code] }

  transparent inline def unpacker[Code[⋅⋅[_]] <: AnyKind]: Any =
    ${ unpackerImpl[Code] }

  // returns 《Code》[As⋅⋅] => Box[Code, As] =
  transparent inline def pack[Code[⋅⋅[_]] <: AnyKind, As] =
    ${ packImpl[Code, As] }

  transparent inline def pacK[K, Code[⋅⋅[_]] <: AnyKind, As]: Any =
    decodeFull("Box_pacK")[[⋅⋅[_]] =>> Code[⋅⋅] :: As :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [Code0[As <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => () =>
        val packer: [X <: ⋅⋅[K]] => Code0[X] => Box[Code, ⋅⋅[X]] =
          k.splice(Box.packer[Code])
        packer[A0]
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
    insideMacroExpansion {
      import quotes.reflect.*

      val encoding = Encoding()
      import encoding.{TypeLambdaTemplate, decodeTypeLambda}
      val typeLambdaTemplate = decodeTypeLambda[Code]
      import typeLambdaTemplate.{bodyFn, boundsFnFlat, paramNamesFlat}

      def returnType(targs: List[TypeRepr]): TypeRepr =
        boxType(TypeRepr.of[Code], targs)

      PolyFun(
        paramNamesFlat,
        boundsFnFlat,
        "x" :: Nil,
        tparams => bodyFn(tparams) :: Nil,
        tparams => returnType(tparams),
        (targs, args, owner) => {
          returnType(targs).asType match
            case '[t] =>
              '{ ${args(0).asExpr}.asInstanceOf[t] }.asTerm
        },
      ).asExpr
    }

  private def unpackerImpl[Code <: AnyKind](using
    Quotes,
    Type[Code],
  ): Expr[Any] =
    insideMacroExpansion {
      import quotes.reflect.*

      inside(TypeRepr.of[Code]) {
        val encoding = Encoding()
        import encoding.{TypeLambdaTemplate, decodeTypeLambda}
        val typeLambdaTemplate = decodeTypeLambda[Code]
        import typeLambdaTemplate.{bodyFn, boundsFnFlat, paramNamesFlat}

        def paramType(targs: List[TypeRepr]): TypeRepr =
          boxType(TypeRepr.of[Code], targs)

        PolyFun(
          paramNamesFlat,
          boundsFnFlat,
          "x" :: Nil,
          tparams => paramType(tparams) :: Nil,
          tparams => bodyFn(tparams),
          (targs, args, owner) => {
            bodyFn(targs).asType match
              case '[t] =>
                '{ ${args(0).asExpr}.asInstanceOf[t] }.asTerm
          },
        ).asExpr
      }
    }

  private def packImpl[Code[⋅⋅[_]] <: AnyKind, As](using
    Quotes,
    Type[Code],
    Type[As],
  ): Expr[Nothing => Box[Code, As]] =
    import quotes.reflect.*

    insideMacroExpansion:
      Encoding().decodeParameterizedType[Code, As] match
        case '[t] =>
          '{ (x: t) => x.asInstanceOf[Box[Code, As]] }

  private def unpackImpl[Code[⋅⋅[_]] <: AnyKind, As](box: Expr[Box[Code, As]])(using
    Quotes,
    Type[Code],
    Type[As],
  ): Expr[Any] =
    insideMacroExpansion:
      Encoding().decodeParameterizedType[Code, As] match
        case '[t] => '{ $box.asInstanceOf[t] }
}
