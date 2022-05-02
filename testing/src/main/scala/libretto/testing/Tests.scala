package libretto.testing

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

  class Case[TDSL <: TestDsl] private (using val tdsl: TDSL)(
    val body: tdsl.TestCase,
    val resultTrans: TestResult => TestResult,
  )

  object Case {
    def apply(using tdsl: TestDsl)(body: tdsl.TestCase): Case[tdsl.type] =
      new Case[tdsl.type]()(body, identity[TestResult])

    def assertCrashes(using tdsl: TestDsl)(body: tdsl.TestCase): Case[tdsl.type] =
      assertCrashes_(body, None)

    def assertCrashesWith(using tdsl: TestDsl)(expectedErrorMessage: String)(body: tdsl.TestCase): Case[tdsl.type] =
      assertCrashes_(body, Some(expectedErrorMessage))

    private def assertCrashes_(using tdsl: TestDsl)(body: tdsl.TestCase, withMessage: Option[String]): Case[tdsl.type] =
      new Case[tdsl.type]()(
        body,
        {
          case TestResult.Crash(e) =>
            withMessage match {
              case None =>
                TestResult.Success
              case Some(msg) =>
                if (e.getMessage == msg)
                  TestResult.Success
                else
                  TestResult.Failure(s"Expected message $msg, actual exception: $e")
            }
          case TestResult.Success =>
            TestResult.Failure("Expected crash, but the program completed successfully.")
          case TestResult.Failure(msg) =>
            TestResult.Failure(s"Expected crash, but the program completed with failure: $msg.")
        },
      )

    extension (name: String) {
      def >>(using tdsl: TestDsl)(body: tdsl.TestCase): (String, Case[tdsl.type]) =
        (name, Case(body))
    }
  }
}
