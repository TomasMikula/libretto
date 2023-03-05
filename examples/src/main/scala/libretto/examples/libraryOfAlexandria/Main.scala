package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterApp
import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

import vendor.{Page, ScrollId}

object Main extends StarterApp {
  val ScrollIds = List(
    ScrollId("ISBN 316148410-0"),
    ScrollId("ISBN 316148411-0"),
    ScrollId("ISBN 316148412-0"),
    ScrollId("ISBN 316148413-0"),
    ScrollId("ISBN 316148414-0"),
    ScrollId("ISBN 316148415-0"),
    ScrollId("ISBN 316148416-0"),
    ScrollId("ISBN 316148417-0"),
    ScrollId("ISBN 316148418-0"),
    ScrollId("ISBN 316148419-0"),
    ScrollId("ISBN 316148420-0"),
    ScrollId("ISBN 316148421-0"),
    ScrollId("ISBN 316148422-0"),
    ScrollId("ISBN 316148423-0"),
    ScrollId("ISBN 316148424-0"),
    ScrollId("ISBN 316148425-0"),
    ScrollId("ISBN 316148426-0"),
    ScrollId("ISBN 316148427-0"),
    ScrollId("ISBN 316148428-0"),
    ScrollId("ISBN 316148429-0"),
  )

  override def blueprint: Done -⚬ Done = {
    val downloader = Downloader(ConnectorModuleImpl)
    λ.+ { start =>
      val connector = ConnectorModuleImpl.createConnector(start)
      val scrollIds = ValSource.fromList(ScrollIds)(start)
      (connector |*| scrollIds)
      :>> downloader.downloadAll(prepareAhead = 10)
      :>> ValSource.forEachSequentially(printPage)
    }
  }

  private def printPage: Val[Page] -⚬ Done =
    printLine { case Page(scrollId, pageNumber, content) =>
      s"${scrollId.value} page ${pageNumber}\n${content}"
    }
}
