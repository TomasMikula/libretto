package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

class Downloader(val api: ConnectorApi) {
  def blueprint: (api.Connector |*| ValSource[ScrollId]) -⚬ ValSource[Page] =
    fetchForEach
     > Source.prefetch(10)(discardPrefetched = ValSource.close)
     > Source.flatten

  private def fetchForEach: (api.Connector |*| ValSource[ScrollId]) -⚬ Source[ValSource[Page]] =
    rec { fetchForEach =>
      λ { case connector |*| ids =>
        producing { pagess =>
          (Source.fromChoice >>: pagess) switch {
            case Left(closing) =>
              closing := Source.close(ids)
            case Right(pulling) =>
              pulling :=
                Source.poll(ids) switch {
                  case Left(closed) =>
                    Source.Polled.empty(closed)
                  case Right(id |*| ids) =>
                    Source.Polled.cons(api.fetch(connector |*| id) |*| fetchForEach(connector |*| ids))
                }
          }
        }
      }
    }
}
