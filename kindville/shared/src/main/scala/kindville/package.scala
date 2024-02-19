package kindville

import scala.quoted.*
import scala.PolyFunction
import scala.annotation.experimental

sealed trait *
sealed trait ->[K, L]

sealed trait ::[H <: AnyKind, T]
sealed trait TNil

sealed trait ofKind[F <: AnyKind, K]
sealed trait ofKinds[As, Ks]

extension [FA](fa: FA)
  transparent inline def unmask[F <: AnyKind, As](using ev: TypeApp[F, As, FA]): Any =
    ${ unmaskImpl('fa, 'ev) }

/** Returns `[A1, ...] => F[A1, ...] => R`. */
@experimental
transparent inline def encoderOf[F <: AnyKind, R](
  f: [As, FAs] => (FAs, TypeApp[F, As, FAs]) => R,
  ): Any =
    ${ encoderImpl[F, R]('f) }

@experimental
private[kindville] def encoderImpl[F <: AnyKind, R](
  f: Expr[[As, FAs] => (FAs, TypeApp[F, As, FAs]) => R],
)(using
  Quotes,
  Type[F],
  Type[R],
): Expr[Any] =
  import quotes.reflect.*
  TypeRepr.of[F] match
    case bindingType @ TypeLambda(paramNames, paramBounds, body) =>
      val applyMethodType: TypeRepr =
        PolyType(paramNames)(
          pt => paramBounds, // TODO: substitute //.map(_.substituteTypes(from = List(bindingType.typeSymbol), to = List(pt)).asInstanceOf[TypeBounds]),
          pt => MethodType(
            List("f"),
          )(
            _ => List(bindingType.appliedTo(List.range(0, paramNames.size).map(i => pt.param(i)))),
            _ => TypeRepr.of[R],
          ),
        )
      val resultType: TypeRepr =
        Refinement(
          TypeRepr.of[PolyFunction],
          "apply",
          applyMethodType,
        )
      val t: Type[Any] = resultType.asType.asInstanceOf[Type[Any]]
      // '{ ??? }.asExprOf(using t)
      val parents = List(TypeTree.of[Object], TypeTree.of[PolyFunction])
      val clsSym = Symbol.newClass(
        Symbol.spliceOwner,
        name = "$anon",
        parents = parents.map(_.tpe),
        decls = cls => List(
          Symbol.newMethod(cls, "apply", applyMethodType),
        ),
        selfType = None,
      )
      val applySym = clsSym.declaredMethod("apply").head
      val applyDef =
        DefDef(
          applySym,
          argss => {
            val List(targs, args) = argss
            Some(
              ???
              // TODO: f takes [As, FAs](FAs, TypeApp[F, As, FAs])
              // f.asTerm
              //   .appliedToTypeTrees(targs.map(_.asInstanceOf[TypeTree]))
              //   .appliedToArgs(args.map(_.asInstanceOf[Term]))
            )
          },
        )
      val clsDef = ClassDef(clsSym, parents, List(applyDef))
      val newCls = Apply(Select(New(TypeIdent(clsSym)), clsSym.primaryConstructor), args = Nil)
      Block(
        List(clsDef),
        newCls
      ).asExpr

      // '{ [V] => (f: Map[Int, V]) => f.size }.asExprOf(using t)
    case other =>
      // val fs = Printer.TypeReprShortCode.show(other)
      val fs = Printer.TypeReprStructure.show(other)
      report.error(s"Implementation restriction: works only for type lambdas. Please, eta-expand $fs to a type lambda manually.")
      '{ ??? }

private[kindville] def unmaskImpl[F <: AnyKind, As, FA](
  fa: Expr[FA],
  ev: Expr[TypeApp[F, As, FA]],
)(using
  Quotes,
  Type[F],
  Type[As],
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

private[kindville] inline def termStructureOf[A](a: A): String =
  ${ printTermStructure('a) }

private[kindville] inline def typeStructureOf[A <: AnyKind]: String =
  ${ printTypeStructure[A] }

private def printTermStructure[A](a: Expr[A])(using Quotes): Expr[String] =
  import quotes.reflect.*
  Expr(Printer.TreeStructure.show(a.asTerm))
  val x = '{ new PolyFunction { override def apply[x, y](m: Map[x, y]): Int = m.size } }
  Expr(Printer.TreeStructure.show(x.asTerm))


private def printTypeStructure[A <: AnyKind](using Quotes, Type[A]): Expr[String] =
  import quotes.reflect.*
  TypeRepr.of[A] match
    case TypeLambda(_, _, AppliedType(_, args)) =>
      Expr(args.collect { case ParamRef(binder, _) => Printer.TypeReprStructure.show(binder) }.head)
    case _ =>
      Expr(Printer.TypeReprStructure.show(TypeRepr.of[A]))