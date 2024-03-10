package kindville

import scala.quoted.*
import kindville.Reporting.*

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

    Encoding().decodeType[As, Code] match
      case '[t] =>
        '{ (x: t) => x }
          .asExprOf[t => Box[As, Code]]

  private def unpackImpl[As, Code <: AnyKind](box: Expr[Box[As, Code]])(using
    Quotes,
    Type[As],
    Type[Code],
  ): Expr[Any] =
    Encoding().decodeType[As, Code] match
      case '[t] => '{ $box.asInstanceOf[t] }
}
