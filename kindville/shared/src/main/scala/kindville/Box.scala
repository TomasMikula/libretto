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
    decodeFull[[⋅⋅[_]] =>> Code[⋅⋅] :: As :: TNil](
      [⋅⋅[_]] => (k: Kuotes[⋅⋅]) ?=> [Code0[As <: ⋅⋅[K]], A0 <: ⋅⋅[K]] => () =>
        val packer: [X <: ⋅⋅[K]] => Code0[X] => Box[Code, ⋅⋅[X]] =
          k.splice(Box.packer[Code])
        packer[A0]
    )

  extension [Code[⋅⋅[_]] <: AnyKind, As](box: Box[Code, As]) {
    transparent inline def unpack: Any =
      ${ unpackImpl[Code, As]('box) }
  }

  private def boxType(using Quotes)(
    code: qr.TypeRepr,
    argGroups: Groups[qr.TypeRepr],
  ): qr.TypeRepr =
    val bundledGroups = argGroups.mapGroups:
      case SingleOrMultiple.Single(t) => t
      case SingleOrMultiple.Multiple(ts) => Encoding.bundleTypeArgs(ts)

    qr.TypeRepr
      .of[Box]
      .appliedTo(
        code ::
        Encoding.bundleTypeArgs(bundledGroups) ::
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
      import typeLambdaTemplate.{bodyFn, boundsFnFlat, paramNames, paramNamesFlat}

      def returnType(targs: List[TypeRepr]): TypeRepr =
        val groupedTArgs: Groups[TypeRepr] =
          paramNames
            .zipWithListUnsafe(targs)
            .map(_._2)
        boxType(TypeRepr.of[Code], groupedTArgs)

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
        import typeLambdaTemplate.{bodyFn, boundsFnFlat, paramNames, paramNamesFlat}

        def paramType(targs: List[TypeRepr]): TypeRepr =
          val groupedTArgs: Groups[TypeRepr] =
            paramNames
              .zipWithListUnsafe(targs)
              .map(_._2)
          boxType(TypeRepr.of[Code], groupedTArgs)

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
