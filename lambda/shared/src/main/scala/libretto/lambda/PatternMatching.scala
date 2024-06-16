package libretto.lambda

import libretto.lambda.util.{Applicative, BiInjective, Exists, NonEmptyList, TypeEq, Validated}
import libretto.lambda.util.TypeEq.Refl
import libretto.lambda.util.Validated.{Invalid, Valid, invalid}

class PatternMatching[-⚬[_, _], |*|[_, _]](using
  SemigroupalCategory[-⚬, |*|],
  BiInjective[|*|],
) {
  import libretto.lambda.Extractor

  type Extractor[A, B] =
    libretto.lambda.Extractor[-⚬, |*|, A, B]

  type Pattern[A, B] =
    AForest[Extractor, |*|, A, B]

  enum PatternMatchError:
    case IncompatibleExtractors(base: Extractor[?, ?], incompatible: NonEmptyList[Extractor[?, ?]])
    case NonExhaustiveness(ext: Extractor[?, ?]) // TODO: include context

  import PatternMatchError.*

  def compilePatternMatch[A, R](
    cases: NonEmptyList[Exists[[Y] =>> (Pattern[A, Y], Y -⚬ R)]],
  ): Validated[
    PatternMatchError,
    A -⚬ R
  ] =
    withFirstScrutineeOf(cases.head.value._1)(
      { case TypeEq(Refl()) =>
        // the first case catches all, remaining cases ignored
        Valid(cases.head.value._2.from[A])
      },
      [F[_], T] => (
        pos: Focus[|*|, F],
        scr: Partitioning[-⚬, |*|, T],
        ev:  A =:= F[T],
      ) =>
        ev match { case TypeEq(Refl()) =>
          scr.compileAt(
            pos,
            [X] => (p: scr.Partition[X]) => {
              val ext: Extractor[T, X] =
                Extractor(scr, p)
              collectMatchingCases[F, T, X, R](cases.toList, pos, ext) match
                case Valid(matchingCases) =>
                  matchingCases match
                    case Nil =>
                      invalid(NonExhaustiveness(ext)) // TODO: include context of this extractor
                    case c :: cs =>
                      compilePatternMatch[F[X], R](NonEmptyList(c, cs))
                case Invalid(incompatibleExtractors) =>
                  invalid(IncompatibleExtractors(ext, incompatibleExtractors))
            }
          ).map(_.from[A])
        }
    )

  private def withFirstScrutineeOf[A, B, R](p: Pattern[A, B])(
    caseCatchAll: (A =:= B) => R,
    caseProper: [F[_], T] => (Focus[|*|, F], Partitioning[-⚬, |*|, T], A =:= F[T]) => R,
  ): R =
    p match
      case AForest.Node(extr, _) =>
        caseProper[[x] =>> x, A](Focus.id, extr.partitioning, summon)
      case AForest.Empty() =>
        caseCatchAll(summon)
      case AForest.Par(p1, p2) =>
        withFirstScrutineeOfPar(p1, p2)(caseCatchAll, caseProper)

  private def withFirstScrutineeOfPar[A1, A2, B1, B2, R](
    p1: Pattern[A1, B1],
    p2: Pattern[A2, B2],
  )(
    caseCatchAll: ((A1 |*| A2) =:= (B1 |*| B2)) => R,
    caseProper: [F[_], T] => (Focus[|*|, F], Partitioning[-⚬, |*|, T], (A1 |*| A2) =:= F[T]) => R,
  ): R =
    withFirstScrutineeOf(p1)(
      caseProper = { [F1[_], T1] => (f1: Focus[|*|, F1], ex1: Partitioning[-⚬, |*|, T1], ev1: A1 =:= F1[T1]) =>
        type F[T] = F1[T] |*| A2
        caseProper[F, T1](f1.inFst[A2], ex1, ev1.liftCo[[t] =>> t |*| A2])
      },
      caseCatchAll = { case TypeEq(Refl()) =>
        withFirstScrutineeOf(p2)(
          caseProper = { [F2[_], T2] => (f2: Focus[|*|, F2], ex2: Partitioning[-⚬, |*|, T2], ev2: A2 =:= F2[T2]) =>
            type F[T] = A1 |*| F2[T]
            caseProper[F, T2](f2.inSnd[A1], ex2, ev2.liftCo[[t] =>> A1 |*| t])
          },
          caseCatchAll = { case TypeEq(Refl()) =>
            caseCatchAll(summon)
          },
        )
      },
    )

  private def collectMatchingCases[F[_], T, U, R](
    cases: List[Exists[[Y] =>> (Pattern[F[T], Y], Y -⚬ R)]],
    pos: Focus[|*|, F],
    ext: Extractor[T, U],
  ): Validated[
    Extractor[?, ?], // incompatible extractors at the given position
    List[Exists[[Y] =>> (Pattern[F[U], Y], Y -⚬ R)]],
  ] =
    Applicative.traverseList(cases) {
      case Exists.Some((pattern, handler)) =>
        positExtractor(ext, pos, pattern, handler)
    }.map(_.flatten)

  private def positExtractor[T, U, F[_], Y, R](
    ext: Extractor[T, U],
    pos: Focus[|*|, F],
    pattern: Pattern[F[T], Y],
    handler: Y -⚬ R,
  ): Validated[
    Extractor[?, ?], // incompatible extractor at the given position in the given pattern
    Option[Exists[[Y] =>> (Pattern[F[U], Y], Y -⚬ R)]],
  ] =
    pattern.focus(pos) match
      case r: AForest.Focused.At[arr, pr, f, t, y, g] =>
        summon[Y =:= g[y]]
        val subpattern: Pattern[T, y] = r.target
        subpattern match
          case AForest.Empty() =>
            summon[T =:= y]
            val pattern1: Pattern[F[U], g[U]] = r.context[U]
            val handler1: g[U] -⚬ R = ext.reinject.at(r.context.outFocus) > handler
            Validated.Valid(Some(Exists((pattern1, handler1))))
          case AForest.Node(ext1, subpattern1) =>
            (ext sameAs ext1) match
              case None =>
                // incompatible partitionings
                Validated.invalid(ext1)
              case Some(None) =>
                // non-matching partitions
                Validated.Valid(None)
              case Some(Some(TypeEq(Refl()))) =>
                val pattern1 = r.context.plug(subpattern1)
                Validated.Valid(Some(Exists((pattern1, handler))))
          case AForest.Par(sp1, sp2) =>
            libretto.lambda.UnhandledCase.raise(s"incompatible extractors: $ext vs ($sp1, $sp2)")
      case AForest.Focused.IntoNode(fo, fi, node) =>
        Validated.invalid(node.value)
}
