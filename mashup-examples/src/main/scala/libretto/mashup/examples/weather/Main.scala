package libretto.mashup.examples.weather

import zio.{ZIO, ZIOAppDefault}

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

  override def run: ZIO[Any, Nothing, Unit] =
    for {
      // start mocks of input services
      _ <- WeatherService.start(weather.host, weather.port).forkDaemon
      _ <- TemperatureConverterService.start(converter.host, converter.port).forkDaemon

      // start the mash-up service
      _ <- PragueWeatherService.start(weather.uri, converter.uri, mashup.host, mashup.port)
    } yield ()
}
