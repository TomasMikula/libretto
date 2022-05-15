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

      val body: Done -⚬ O

      val conductor: OutPort[O] => Outcome[Unit]
    }

    case class Multiple[TDSL <: TestDsl](
      cases: NonEmptyList[(String, Case[TDSL])],
    ) extends Case[TDSL]

    private def make[A](using
      tdsl: TestDsl,
    )(
      body0: dsl.-⚬[dsl.Done, A],
      conductor0: tdsl.probes.OutPort[A] => tdsl.Outcome[Unit],
    ): Case[tdsl.type] =
      new Single[tdsl.type] {
        override type O = A
        override val testDsl = tdsl
        override val body = body0
        override val conductor = conductor0
      }

    def apply(using tdsl: TestDsl)(body: tdsl.TestCase): Case[tdsl.type] =
      make(body, tdsl.extractTestResult)

    def apply[O](using tdsl: TestDsl)(
      body: tdsl.dsl.-⚬[tdsl.dsl.Done, O],
      conduct: tdsl.probes.OutPort[O] => tdsl.Outcome[Unit],
    ): Case[tdsl.type] =
      make[O](body, conduct)

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
    }

    def assertCrashes(using tdsl: TestDsl)(body: tdsl.TestCase): Case[tdsl.type] =
      assertCrashes_(body, None)

    def assertCrashesWith(using tdsl: TestDsl)(expectedErrorMessage: String)(body: tdsl.TestCase): Case[tdsl.type] =
      assertCrashes_(body, Some(expectedErrorMessage))

    private def assertCrashes_(using tdsl: TestDsl)(body: tdsl.TestCase, withMessage: Option[String]): Case[tdsl.type] = {
      import tdsl.{F, Outcome}

      make(
        body,
        port => Outcome(
          Outcome.unwrap(tdsl.extractTestResult(port)).map {
            case TestResult.Crash(e) =>
              withMessage match {
                case None =>
                  TestResult.Success(())
                case Some(msg) =>
                  if (e.getMessage == msg)
                    TestResult.Success(())
                  else
                    TestResult.Failure(s"Expected message $msg, actual exception: $e")
              }
            case TestResult.Success(_) =>
              TestResult.Failure("Expected crash, but the program completed successfully.")
            case TestResult.Failure(msg) =>
              TestResult.Failure(s"Expected crash, but the program completed with failure: $msg.")
          }
        ),
      )
    }
  }
}
