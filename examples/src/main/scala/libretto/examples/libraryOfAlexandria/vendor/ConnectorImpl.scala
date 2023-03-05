package libretto.examples.libraryOfAlexandria.vendor

private[vendor] class ConnectorImpl extends Connector {
  private var openConnections: Int = 0
  private var closed: Boolean = false

  override def connect(): Connection =
    ConnectorImpl.this.synchronized {
      if (closed) {
        throw IllegalStateException("Already closed")
      } else {
        openConnections += 1
        new ConnectionImpl()
      }
    }

  override def close(): Unit =
    ConnectorImpl.this.synchronized {
      if (openConnections > 0)
        throw IllegalStateException(s"There are $openConnections open connections")
      else
        closed = true
    }

  class ConnectionImpl() extends Connection {
    private var closed = false
    private var inUseBy: Option[Job[?]] = None

    override def fetchScroll(id: ScrollId): Option[ResultSet[Page]] = {
      val job: Option[ScrollDigitization] =
        ConnectionImpl.this.synchronized {
          if (closed) {
            throw IllegalStateException("Connection already closed.")
          } else if (inUseBy.nonEmpty) {
            throw IllegalStateException("Connection already in use.")
          } else {
            val job: Option[ScrollDigitization] =
              ScrollDatabase.get(id).map(ScrollDigitization(id, _))
            inUseBy = job
            job
          }
        }
      job.map(_.start())
    }

    override def close(): Unit = {
      val currentJob: Option[Job[?]] =
        ConnectionImpl.this.synchronized {
          if (!closed) {
            val currentJob = inUseBy
            inUseBy = None
            closed = true
            ConnectorImpl.this.synchronized {
              openConnections -= 1
            }
            currentJob
          } else {
            None
          }
        }
      currentJob.foreach(_.cancel())
    }

    sealed trait Job[A] {
      def start(): A
      def cancel(): Unit
    }

    class ScrollDigitization(id: ScrollId, scroll: Scroll) extends Job[ResultSet[Page]] {
      private var started = false
      private var closed  = false

      override def start(): ResultSet[Page] =
        ScrollDigitization.this.synchronized {
          if (started)
            throw IllegalStateException("Job already started")
          else {
            started = true
            Thread.sleep(10) // scanning the scroll takes some time
            new ResultSetImpl(id, scroll.paginate())
          }
        }

      override def cancel(): Unit =
        ScrollDigitization.this.synchronized {
          if (!closed) {
            closed = true
            ConnectionImpl.this.synchronized {
              ConnectionImpl.this.inUseBy match {
                case None =>
                  // do nothing
                case Some(job) =>
                  assert(job eq ScrollDigitization.this)
                  ConnectionImpl.this.inUseBy = None
              }
            }
          }
        }

      class ResultSetImpl(
        scrollId: ScrollId,
        pages: Iterator[(Int, String)],
      ) extends ResultSet[Page] {
        override def earlyClose(): Unit =
          ScrollDigitization.this.cancel()

        override def next(): Option[Page] =
          if (pages.hasNext) {
            val (number, content) = pages.next()
            Some(Page(scrollId, number, content))
          } else {
            ScrollDigitization.this.cancel()
            None
          }
      }
    }
  }
}
