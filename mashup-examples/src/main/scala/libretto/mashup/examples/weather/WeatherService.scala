package libretto.mashup.examples.weather

import zio.ZIO
import libretto.mashup.{Input, Output, Service}
import libretto.mashup.dsl.{-->, ##, EmptyResource, Expr, Float64, Fun, Record, Text, closure, fun, of}
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

  type City =
    Text

  type Celsius =
    Record ## ("celsius" of Float64)

  object Celsius {
    def apply(value: Expr[Float64]): Expr[Celsius] =
      Record().##["celsius"](value)

    def apply(value: Double): Expr[Celsius] =
      Celsius(Float64(value))
  }

  type WeatherReport = (
    Record
      ## ("city"        of City)
      ## ("temperature" of Celsius)
  )

  object WeatherReport {
    def apply(city: Expr[City], temperature: Expr[Celsius]): Expr[WeatherReport] =
      Record()
        .##["city"](city)
        .##["temperature"](temperature)
  }

  def blueprint: Fun[EmptyResource, City --> WeatherReport] =
    fun { emptyResource =>
      closure { city =>
        WeatherReport(city, Celsius(23.5))
      }
    }

  def restApi: RestApi[City --> WeatherReport] =
    RestApi(endpoint)

  def endpoint: Endpoint[City, WeatherReport] =
    Endpoint
      .get(path[City])
}
