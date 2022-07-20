package libretto.mashup.examples.weather

import libretto.mashup.{Input, Runtime}

import java.util.concurrent.Executors
import zio.{Scope, ZIO, ZIOAppDefault}

/**
 * Runs [[PragueWeatherService]].
 * Also starts mocks of general weather service and temperature converter service
 * that are then used by [[PragueWeatherService]].
 *
 * Run using
 *   sbt mashupExamples/run
 * Then go to
 *   http://localhost:8000/
 */
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

  private def acquireRuntime: ZIO[Scope, Nothing, Runtime] =
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
      fiber1 <- WeatherService.start(weather.host, weather.port).forkDaemon
      fiber2 <- TemperatureConverterService.start(converter.host, converter.port).forkDaemon

      // start the mash-up service
      fiber3 <-
        PragueWeatherService.start(
          Input.restApiAt(WeatherService.restApi, weather.uri),
          Input.restApiAt(TemperatureConverterService.restApi, converter.uri),
          mashup.host,
          mashup.port
        ).forkDaemon

      _ <- ZIO.foreachPar(Seq(fiber1, fiber2, fiber3))(_.join)
    } yield ()
}
