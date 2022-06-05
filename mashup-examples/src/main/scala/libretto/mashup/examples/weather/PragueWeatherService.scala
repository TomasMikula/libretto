package libretto.mashup.examples.weather

import zio.ZIO

object PragueWeatherService {
  def start(
    weatherServiceUri: String,
    temperatureConverterUri: String,
    host: String,
    port: Int,
  ): ZIO[Any, Nothing, Unit] =
    ???
}
