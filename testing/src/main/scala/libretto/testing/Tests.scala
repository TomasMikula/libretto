package libretto.testing

import libretto.util.Monad.syntax._
import scala.{:: => NonEmptyList}

sealed trait Tests {
  type Kit <: TestKit

  def testCases(using kit: Kit): NonEmptyList[(String, TestCase[kit.type])]

  val testExecutors: NonEmptyList[TestExecutor[Kit]]
}

object Tests {
  def writtenUsing[TK <: TestKit]: Builder.WrittenUsing[TK] =
    new Builder.WrittenUsing[TK]()

  object Builder {
    class WrittenUsing[TK <: TestKit]() {
      def executedBy(
        executor: TestExecutor[TK],
        executors: TestExecutor[TK]*,
      ): ExecutedBy[TK] =
        new ExecutedBy[TK](NonEmptyList(executor, executors.toList))
    }

    class ExecutedBy[TK <: TestKit](executors: NonEmptyList[TestExecutor[TK]]) {
      def in(
        cases: (kit: TK) ?=> Cases[kit.type],
      ): Tests =
        new Tests {
          override type Kit = TK
          override def testCases(using kit: TK) = cases.values
          override val testExecutors = executors
        }
    }
  }

  sealed trait Cases[TK <: TestKit] {
    def values(using kit: TK): NonEmptyList[(String, TestCase[kit.type])]
  }

  object Cases {
    def apply(using kit: TestKit)(
      testCase: (String, TestCase[kit.type]),
      moreCases: (String, TestCase[kit.type])*,
    ): Cases[kit.type] =
      new Cases[kit.type] {
        override def values(using testKit: kit.type): NonEmptyList[(String, TestCase[testKit.type])] =
          NonEmptyList(testCase, moreCases.toList)
      }
  }
}
