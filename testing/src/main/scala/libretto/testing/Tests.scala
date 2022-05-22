package libretto.testing

import libretto.testing.TestDsl.dsl
import libretto.util.Monad.syntax._
import scala.{:: => NonEmptyList}

sealed trait Tests {
  type TDSL <: TestDsl

  def testCases(using tdsl: TDSL): NonEmptyList[(String, Tests.Case[tdsl.type])]

  val testExecutors: NonEmptyList[TestExecutor[TDSL]]
}

object Tests {
  def use[TDSL <: TestDsl]: Builder.Use[TDSL] =
    new Builder.Use[TDSL]()

  object Builder {
    class Use[TDSL <: TestDsl]() {
      def executedBy(
        executor: TestExecutor[TDSL],
        executors: TestExecutor[TDSL]*,
      ): ExecutedBy[TDSL] =
        new ExecutedBy[TDSL](NonEmptyList(executor, executors.toList))
    }

    class ExecutedBy[TDSL <: TestDsl](executors: NonEmptyList[TestExecutor[TDSL]]) {
      def in(
        cases: (tdsl: TDSL) ?=> Cases[tdsl.type],
      ): Tests = {
        type TDSL0 = TDSL
        new Tests {
          override type TDSL = TDSL0
          override def testCases(using tdsl: TDSL) = cases.values
          override val testExecutors = executors
        }
      }
    }
  }

  sealed trait Cases[TDSL <: TestDsl] {
    def values(using tdsl: TDSL): NonEmptyList[(String, Case[tdsl.type])]
  }

  object Cases {
    def apply(using tdsl: TestDsl)(
      testCase: (String, Case[tdsl.type]),
      moreCases: (String, Case[tdsl.type])*,
    ): Cases[tdsl.type] =
      new Cases[tdsl.type] {
        override def values(using testDsl: tdsl.type): NonEmptyList[(String, Case[testDsl.type])] =
          NonEmptyList(testCase, moreCases.toList)
      }
  }

  sealed trait Case[TDSL <: TestDsl]

  object Case {

    sealed trait Single[TDSL <: TestDsl] extends Case[TDSL] {
      val testDsl: TDSL
      import testDsl.Outcome
      import testDsl.dsl._
      import testDsl.probes.OutPort

      type O
      type X

      val body: Done -⚬ O

      val conductor: OutPort[O] => Outcome[X]

      val postStop: X => Outcome[Unit]
    }

    case class Multiple[TDSL <: TestDsl](
      cases: List[(String, Case[TDSL])],
    ) extends Case[TDSL]

    private def make[A, B](using
      tdsl: TestDsl,
    )(
      body0: dsl.-⚬[dsl.Done, A],
      conductor0: tdsl.probes.OutPort[A] => tdsl.Outcome[B],
      postStop0: B => tdsl.Outcome[Unit],
    ): Case[tdsl.type] =
      new Single[tdsl.type] {
        override type O = A
        override type X = B
        override val testDsl = tdsl
        override val body = body0
        override val conductor = conductor0
        override val postStop = postStop0
      }

    def apply(using tdsl: TestDsl)(body: dsl.-⚬[dsl.Done, tdsl.TestResult]): Case[tdsl.type] =
      make(body, tdsl.extractTestResult, tdsl.monadOutcome.pure)

    def apply[O](using tdsl: TestDsl)(
      body: tdsl.dsl.-⚬[tdsl.dsl.Done, O],
      conduct: tdsl.probes.OutPort[O] => tdsl.Outcome[Unit],
    ): Case[tdsl.type] =
      make[O, Unit](body, conduct, tdsl.monadOutcome.pure)

    def apply[A, B](using tdsl: TestDsl)(
      body: tdsl.dsl.-⚬[tdsl.dsl.Done, A],
      conduct: tdsl.probes.OutPort[A] => tdsl.Outcome[B],
      postStop: B => tdsl.Outcome[Unit],
    ): Case[tdsl.type] =
      make[A, B](body, conduct, postStop)

    def multiple[TDSL <: TestDsl](
      cases: (String, Case[TDSL])*,
    ): Case[TDSL] =
      Multiple[TDSL](cases.toList)

    def interactWith[O](using tdsl: TestDsl)(body: tdsl.dsl.-⚬[tdsl.dsl.Done, O]): InteractWith[tdsl.type, O] =
      InteractWith(tdsl, body)

    object InteractWith {
      def apply[O](tdsl: TestDsl, body: tdsl.dsl.-⚬[tdsl.dsl.Done, O]): InteractWith[tdsl.type, O] =
        new InteractWith(tdsl, body)
    }

    class InteractWith[TDSL <: TestDsl, O](
      val tdsl: TDSL,
      val body: tdsl.dsl.-⚬[tdsl.dsl.Done, O],
    ) {
      def via(conductor: tdsl.probes.OutPort[O] => tdsl.Outcome[Unit]): Case[tdsl.type] =
        Case(using tdsl)(body, conductor)

      def via[X](
        conductor: tdsl.probes.OutPort[O] => tdsl.Outcome[X],
        postStop: X => tdsl.Outcome[Unit],
      ): Case[tdsl.type] =
        Case(using tdsl)(body, conductor, postStop)
    }

    def assertCrashes(using tdsl: TestDsl)(body: dsl.-⚬[dsl.Done, dsl.Done]): Case[tdsl.type] = {
      Case[dsl.Done](
        body,
        port => tdsl.expectCrashDone(port).void,
      )
    }

    def assertCrashesWith(using tdsl: TestDsl)(expectedErrorMessage: String)(body: dsl.-⚬[dsl.Done, dsl.Done]): Case[tdsl.type] = {
      import tdsl.Outcome

      Case[dsl.Done](
        body,
        port => tdsl.expectCrashDone(port).flatMap {
          case e if expectedErrorMessage == e.getMessage =>
            Outcome.success(())
          case e =>
            Outcome.failure(s"Expected message $expectedErrorMessage, actual exception: $e")
        },
      )
    }
  }
}
