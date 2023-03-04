package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit._
import libretto.stream.scaletto.DefaultStreams._

import vendor.{Page, ScrollId}

object ConnectorModuleImpl extends ConnectorModule {
  override opaque type Connector = RefCounted[vendor.Connector]

  private type Connection = Connector |*| Res[vendor.Connection]

  override def fetchScroll: (Connector |*| Val[ScrollId]) -⚬ ValSource[Page] =
    fst(connect) > assocLR > snd(fetch > ValSource.notifyUpstreamClosed) >
      λ { case connector |*| (pageSrcClosed |*| pageSrc) =>
        val connectorClosed = RefCounted.releaseOnPing(pageSrcClosed |*| connector)
        ValSource.delayClosedBy(connectorClosed |*| pageSrc)
      }

  def createConnector: Done -⚬ Connector =
    constVal(()) > RefCounted.acquire0(
      _ => vendor.Connector.newInstance(),
      release = _.close(),
    )

  private def connect: Connector -⚬ Connection =
    RefCounted.effectRdAcquire(_.connect(), Some(_.close()))

  private def fetch: (Res[vendor.Connection] |*| Val[ScrollId]) -⚬ ValSource[Page] =
    ???
}
