package libretto.mashup.examples.weather

import libretto.mashup.Runtime

import java.util.concurrent.Executors
import zio.{Scope, ZIO, ZIOAppDefault}

object Main extends ZIOAppDefault {
  private object weather {
    val host = "localhost"
    val port = 8001
    val uri  = s"http://$host:$port"
  }

  private object converter {
    val host = "localhost"
    val port = 8002
    val uri  = s"http://$host:$port"
  }

  private object mashup {
    val host = "localhost"
    val port = 8000
  }

  override def run: ZIO[Any, Throwable, Unit] =
    ZIO.scoped(
      for {
        runtime <- acquireRuntime
        _       <- run(using runtime)
      } yield ()
    )

  private def acquireRuntime =
    ZIO
      .acquireRelease(
        ZIO.succeed(Executors.newScheduledThreadPool(java.lang.Runtime.getRuntime().availableProcessors())),
      )(
        executor => ZIO.succeed(executor.shutdownNow()),
      )
      .map(Runtime.create)

  private def run(using runtime: Runtime): ZIO[Scope, Throwable, Unit] =
    for {
      // start mocks of input services
      _ <- WeatherService.start(weather.host, weather.port)//.forkDaemon
              .tapErrorCause(c => ZIO.logCause(c))
      // _ <- TemperatureConverterService.start(converter.host, converter.port).forkDaemon

      // // start the mash-up service
      // _ <- PragueWeatherService.start(weather.uri, converter.uri, mashup.host, mashup.port)
    } yield ()
}
