package libretto

import libretto.lambda.Extractor
import libretto.lambda.util.Monad.syntax.*
import libretto.lambda.util.SourcePos
import libretto.scaletto.ScalettoLib
import libretto.testing.TestCase
import libretto.testing.scaletto.ScalettoTestKit
import libretto.testing.scalatest.scaletto.ScalatestScalettoTestSuite
import scala.annotation.targetName

class MutualRecursionTests extends ScalatestScalettoTestSuite {

  override def testCases(using kit: ScalettoTestKit): List[(String, TestCase[kit.type])] = {
    import kit.{OutPort as _, *}
    import kit.dsl.{*, given}

    val coreLib = CoreLib(kit.dsl)
    val scalettoLib = ScalettoLib(kit.dsl, coreLib)
    import coreLib.{*, given}
    import scalettoLib.{*, given}

    /** A non-empty list of `A`'s, followed by a terminator of type `T`. */
    type TerminatedNEL[A, T] = Rec[[X] =>> A |*| (T |+| X)]

    object TerminatedNEL {
      def extract[A, T]: Extractor[-⚬, |*|, TerminatedNEL[A, T], A |*| (T |+| TerminatedNEL[A, T])] =
        Extractor
          .identity[-⚬, |*|, A |*| (T |+| TerminatedNEL[A, T])](using dsl.category)
          .afterUnpack

      /** Alias for [[extract]]. */
      def apply[A, T]: Extractor[-⚬, |*|, TerminatedNEL[A, T], A |*| (T |+| TerminatedNEL[A, T])] =
        extract[A, T]
    }

    /** A non-empty list of Σ's interspersed with non-empty sequences of Δ's.
     * Example usage: Σ's are snapshots (i.e. full states), Δ's are diffs from the previous states.
     *   To have a new snapshot, there needs to be at least one diff in between.
     */
    type ΣΔList[Σ, Δ] = Rec[[X] =>> Σ |*| (One |+| TerminatedNEL[Δ, X])]

    object ΣΔList {
      type NETail[Σ, Δ] = TerminatedNEL[Δ, ΣΔList[Σ, Δ]]
      type Tail[Σ, Δ] = One |+| NETail[Σ, Δ]

      def extract[Σ, Δ]: Extractor[-⚬, |*|, ΣΔList[Σ, Δ], Σ |*| Tail[Σ, Δ]] =
        Extractor
          .identity(using dsl.category)
          .afterUnpack

      /** Alias for [[extract]]. */
      def apply[Σ, Δ]: Extractor[-⚬, |*|, ΣΔList[Σ, Δ], Σ |*| Tail[Σ, Δ]] =
        extract[Σ, Δ]

      def single[Σ, Δ]: Σ -⚬ ΣΔList[Σ, Δ] =
        λ { σ => ΣΔList.apply(σ |*| InL($.one)) }
    }

    extension [Δ](δ: $[Δ]) {
      @targetName("prepend_delta_to_ΣΔList")
      def *:[Σ](xs: $[ΣΔList.NETail[Σ, Δ]])(using SourcePos, LambdaContext): $[ΣΔList.NETail[Σ, Δ]] =
        TerminatedNEL.apply(δ |*| InR(xs))

      @targetName("prepend_delta_to_ΣΔList_Tail")
      def **:[Σ](xs: $[ΣΔList[Σ, Δ]])(using SourcePos, LambdaContext): $[ΣΔList.NETail[Σ, Δ]] =
        TerminatedNEL.apply(δ |*| InL(xs))
    }

    extension [Σ](σ: $[Σ]) {
      @targetName("prepend_sigma_to_ΣΔList_Tail")
      def *::[Δ](xs: $[ΣΔList.NETail[Σ, Δ]])(using SourcePos, LambdaContext): $[ΣΔList[Σ, Δ]] =
        ΣΔList.apply[Σ, Δ](σ |*| InR(xs))
    }

    // mutually recursive with the nested function `go`
    // (that it could easily be rewritten without mutual recursion is beside the point)
    def sigmas[Σ, Δ](using Δ: Closeable[Δ]): ΣΔList[Σ, Δ] -⚬ (LList1[Σ] |*| Done) =
      λ.rec { sigmas => xs =>
        switch(xs)
          .is { case ΣΔList.extract(σ0 |*| InL(u)) => LList1(σ0) |*| done(u) }
          .is { case ΣΔList.extract(σ0 |*| InR(δs)) =>
            val go: LocalFun[TerminatedNEL[Δ, ΣΔList[Σ, Δ]], LList1[Σ] |*| Done] =
              λ.recLocal { go => δs =>
                switch(δs)
                  .is { case TerminatedNEL.extract(δ |*| InL(xs)) =>
                    val σs |*| d = sigmas(xs) // calling outer recursive function `sigmas` from the inner one (`go`)
                    σs |*| join(d |*| Δ.close(δ))
                  }
                  .is { case TerminatedNEL.extract(δ |*| InR(δs)) =>
                    val σs |*| d = go(δs) // calling inner recursive function `go`
                    σs |*| join(d |*| Δ.close(δ))
                  }
                  .end
              }
            val σs |*| d = go(δs)
            LList1.cons1(σ0 |*| σs) |*| d
          }
          .end
      }

    List(
      "sigmas (a mutually recursive function)" -> TestCase
        .interactWith[Val[scala.::[String]]] {
          def σ(using SourcePos, LambdaContext)(s: String): $[Val[String]] =
            constantVal(s)

          λ { case +(d) =>
            val xs: $[ΣΔList[Val[String], Done]] =
              σ("A")
                *:: d *: d **: σ("B")
                *:: d *: d *: d **: σ("C")
                *:: d **: σ("D")
                *:: d *: d *: d **: ΣΔList.single[Val[String], Done](σ("E"))

            sigmas[Val[String], Done](xs) match
              case σs |*| d =>
                toScalaList1(σs) waitFor d
          }
        }.via { port =>
          for {
            ss <- expectVal(port)
            _ <- Outcome.assertEquals(ss, List("A", "B", "C", "D", "E"))
          } yield success
        }
    )
  }


}
