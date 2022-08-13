package libretto.testing.scaletto

import libretto.testing.{TestExecutor, TestSuite}

/** Test suite where all tests are written using [[ScalaTestKit]] (and thus [[libretto.ScalaDSL]]). */
trait ScalettoTestSuite extends TestSuite[ScalettoTestKit] {
  override def testExecutors: List[TestExecutor.Factory[ScalettoTestKit]] =
    List(
      ScalettoTestExecutor.defaultFactory,
    )
}
