package libretto.examples.libraryOfAlexandria

import libretto.scaletto.StarterKit.*
import libretto.stream.scaletto.DefaultStreams.*

import vendor.{Page, ScrollId}

/** Adapts the vendor-provided API for consumption by Libretto.
 * We codify the rules of use, such as
 *  - do not close the connector while it has active connections,
 *  - do not reuse or close a connection while still reading query results
 * so that they cannot be violated by the client Libretto code.
 *
 * There is a clash of two worlds here:
 * sequential, non-linear vs. concurrent, linear.
 */
object ConnectorModuleImpl extends ConnectorModule {
  override opaque type Connector = RefCounted[vendor.Connector]

  override given shareableConnector: CloseableCosemigroup[Connector] with {
    override def split: Connector -⚬ (Connector |*| Connector) =
      RefCounted.dupRef[vendor.Connector]

    override def close: Connector -⚬ Done =
      closeConnector
  }

  override def closeConnector: Connector -⚬ Done =
    RefCounted.release[vendor.Connector]

  // Connection will hold on to connector, thus keeping it alive, until the connection is closed.
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
    RefCounted.effectRdAcquire(
      ScalaFun.blocking(_.connect()),
      Some(ScalaFun.blocking(_.close())),
    )

  /** Initiates fetch even before the downstream pulls, but waits with transfering pages
   *  until downstream pulls.
   */
  private def fetch: (Res[vendor.Connection] |*| Val[ScrollId]) -⚬ ValSource[Page] = {
    val scalaFetch: ScalaFun[(vendor.Connection, ScrollId), Either[Unit, vendor.ResultSet[Page]]] =
      ScalaFun.blocking { case (c, id) => c.fetchScroll(id).toRight(left = ()) }

    val rsClose: ScalaFun[vendor.ResultSet[Page], Unit] =
      ScalaFun.blocking(_.earlyClose())

    λ { case conn |*| id =>
      val conn1 |*| rsOpt = (conn |*| id) |> tryEffectAcquireWr(scalaFetch, Some(rsClose))
      switch ( rsOpt )
        .is { case InL(notFound) =>
          conn1.releaseWhen(neglect(notFound)) |> ValSource.empty[Page]
        }
        .is { case InR(rs) =>
          val (pagesClosed |*| pages) =
            resultSetSource(rs) |> ValSource.notifyUpstreamClosed

          // closing connection only after the result set is closed
          val connClosed = conn1 releaseOnPing pagesClosed

          // for the downstream, delay the pages closed signal until connection is closed
          ValSource.delayClosedBy(connClosed |*| pages)
        }
        .end
    }
  }

  private def resultSetSource: Res[vendor.ResultSet[Page]] -⚬ ValSource[Page] = rec { self =>
    λ { rs =>
      producing { pages =>
        (ValSource.fromChoice >| pages) choose {
          case Left(closing) =>
            closing := rs |> release
          case Right(pulling) =>
            pulling :=
              switch ( nextPage(rs) )
                .is { case InL(closed)      => ValSource.Polled.empty[Page](closed) }
                .is { case InR(page |*| rs) => ValSource.Polled.cons(page |*| self(rs)) }
                .end
        }
      }
    }
  }

  private def nextPage: Res[vendor.ResultSet[Page]] -⚬ (Done |+| (Val[Page] |*| Res[vendor.ResultSet[Page]])) = {
    val nextPageScala: ScalaFun[vendor.ResultSet[Page], Either[Unit, Page]] =
      ScalaFun.blocking { rs => rs.next().toRight(left = ()) }

    effectRd(nextPageScala) > λ { case rs |*| pageOpt =>
      switch ( liftEither(pageOpt) )
        .is { case InL(end)  => injectL(rs releaseWhen neglect(end)) }
        .is { case InR(page) => injectR(page |*| rs) }
        .end
    }
  }
}
