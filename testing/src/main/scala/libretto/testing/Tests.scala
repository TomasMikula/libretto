package libretto.testing

import scala.{:: => NonEmptyList}

sealed trait Tests {
  type TDSL <: TestDsl

  val testCases: NonEmptyList[(String, (tdsl: TDSL) ?=> tdsl.TestCase)]

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
        testCase: (String, (tdsl: TDSL) ?=> tdsl.TestCase),
        moreCases: (String, (tdsl: TDSL) ?=> tdsl.TestCase)*,
      ): Tests = {
        type TDSL0 = TDSL
        new Tests {
          override type TDSL = TDSL0
          override val testCases = NonEmptyList(testCase, moreCases.toList)
          override val testExecutors = executors
        }
      }
    }
  }
}
