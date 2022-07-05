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
          override def testCases(using kit: TK) = cases.get
          override val testExecutors = executors
        }
    }
  }

  sealed trait Cases[TK <: TestKit] {
    def get: NonEmptyList[(String, TestCase[TK])]
  }

  object Cases {
    def apply[TK <: TestKit](
      testCase: (String, TestCase[TK]),
      moreCases: (String, TestCase[TK])*,
    ): Cases[TK] =
      new Cases[TK] {
        override def get: NonEmptyList[(String, TestCase[TK])] =
          NonEmptyList(testCase, moreCases.toList)
      }
  }
}
