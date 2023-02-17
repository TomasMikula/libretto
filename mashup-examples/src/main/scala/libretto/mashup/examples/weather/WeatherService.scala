package libretto.mashup.examples.weather

import libretto.lambda.util.SourcePos
import libretto.mashup.{Input, Output, Runtime, Service}
import libretto.mashup.dsl.{-->, ###, EmptyResource, Expr, Float64, Fun, LambdaContext, Record, Text, alsoElim, closure, fun, of}
import libretto.mashup.rest.{Endpoint, RestApi}
import libretto.mashup.rest.RelativeUrl._
import zio.{Scope, ZIO}

object WeatherService {
  type City =
    Text

  object City {
    def apply(value: String)(using SourcePos, LambdaContext): Expr[City] =
      Text(value)
  }

  type Celsius =
    Record["celsius" of Float64]

  object Celsius {
    def apply(value: Expr[Float64]): Expr[Celsius] =
      Record
        .field("celsius" -> value)

    def apply(value: Double)(using LambdaContext): Expr[Celsius] =
      Celsius(Float64(value))
  }

  type WeatherReport =
    Record[("city"        of City)
        ### ("temperature" of Celsius)
    ]

  object WeatherReport {
    def apply(city: Expr[City], temperature: Expr[Celsius])(using LambdaContext): Expr[WeatherReport] =
      Record
        .field("city"        -> city)
        .field("temperature" -> temperature)
  }

  type WeatherApi =
    City --> WeatherReport

  def start(host: String, port: Int)(using Runtime): ZIO[Scope, Throwable, Unit] =
    Service.runSimple(
      Input.empty,
      Output.restApiAt(
        restApi,
        host,
        port,
      ),
      blueprint,
    )

  def blueprint: Fun[EmptyResource, WeatherApi] =
    fun.? { _ =>
      closure { city =>
        WeatherReport(city, Celsius(23.0))
      }
    }

  def restApi: RestApi[WeatherApi] =
    RestApi(endpoint)

  private def endpoint: Endpoint[City, WeatherReport] =
    Endpoint
      .get(path[City])
}
