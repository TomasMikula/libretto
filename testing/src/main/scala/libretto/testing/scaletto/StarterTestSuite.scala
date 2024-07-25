package libretto.testing.scaletto

import libretto.testing.{TestExecutor, TestSuite}

/** Test suite where all tests are written using [[StarterTestKit]]. */
trait StarterTestSuite extends AbstractScalettoTestSuite[StarterTestKit] {
  override def testExecutors: List[TestExecutor.Factory[StarterTestKit]] =
    List(
      StarterTestExecutor.defaultFactory,
    )
}
