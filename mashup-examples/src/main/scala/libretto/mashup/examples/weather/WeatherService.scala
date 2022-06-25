package libretto.mashup.examples.weather

import zio.ZIO
import libretto.mashup.{Input, Output, Service}
import libretto.mashup.dsl.{##, Float64, Fun, Record, of}
import libretto.mashup.dsl.Fun.-->
import libretto.mashup.rest.{Endpoint, RestApi}
import libretto.mashup.rest.RelativeUrl._

object WeatherService {
  def start(host: String, port: Int): ZIO[Any, Nothing, Unit] =
    Service.run(
      Input.empty,
      Output.restApiAt(
        restApi,
        host,
        port,
      ),
      blueprint,
    )

  type Location =
    String

  type Celsius =
    Record ## ("celsius" of Float64)

  type WeatherReport = (
    Record
      ## ("location"    of String)
      ## ("temperature" of Celsius)
  )

  def blueprint: Fun[Unit, Location --> WeatherReport] =
    ???

  def restApi: RestApi[Location --> WeatherReport] =
    RestApi(endpoint)

  def endpoint: Endpoint[Location, WeatherReport] =
    Endpoint
      .get(path[Location])
}
