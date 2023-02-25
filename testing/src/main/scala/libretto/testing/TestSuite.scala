package libretto.testing

trait TestSuite[Kit <: TestKit] {
  def testExecutors: List[TestExecutor.Factory[Kit]]

  def testCases(using kit: Kit): List[(String, TestCase[kit.type])]

  transparent inline def OutPort(using kit: Kit, exn: kit.bridge.Execution): exn.OutPort.type =
    exn.OutPort

  transparent inline def InPort(using kit: Kit, exn: kit.bridge.Execution): exn.InPort.type =
    exn.InPort
}
