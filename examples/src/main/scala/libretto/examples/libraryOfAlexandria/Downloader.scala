package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

import vendor.{Page, ScrollId}

object Downloader {
  def apply(cm: ConnectorModule): Downloader[cm.type] =
    new Downloader(cm)
}

class Downloader[CM <: ConnectorModule](val cm: CM) {
  def downloadAll(prepareAhead: Int): (cm.Connector |*| ValSource[ScrollId]) -⚬ ValSource[Page] =
    fetchForEach
     > Source.prefetch(prepareAhead)(discardPrefetched = ValSource.close)
     > Source.flatten

  private def fetchForEach: (cm.Connector |*| ValSource[ScrollId]) -⚬ Source[ValSource[Page]] =
    rec { fetchForEach =>
      λ { case +(connector) |*| ids =>
        producing { pagess =>
          (Source.fromChoice >>: pagess) switch {
            case Left(closing) =>
              closing := join(Source.close(ids) |*| cm.closeConnector(connector))
            case Right(pulling) =>
              pulling :=
                Source.poll(ids) switch {
                  case Left(closed) =>
                    join(closed |*| cm.closeConnector(connector)) :>> Source.Polled.empty
                  case Right(id |*| ids) =>
                    val pages  = cm.fetchScroll(connector |*| id)
                    val pagess = fetchForEach(connector |*| ids)
                    Source.Polled.cons(pages |*| pagess)
                }
          }
        }
      }
    }
}
