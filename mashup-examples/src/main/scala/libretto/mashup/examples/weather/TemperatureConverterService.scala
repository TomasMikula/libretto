package libretto.mashup.examples.weather

import libretto.mashup.{Input, Output, Runtime, Service}
import libretto.mashup.dsl.{-->, ##, EmptyResource, Expr, Float64, Fun, Record, as, closure, fun, of}
import libretto.mashup.rest.{Endpoint, RelativeUrl, RestApi}
import libretto.mashup.rest.RelativeUrl.{param, path}
import zio.{Scope, ZIO}

object TemperatureConverterService {
  type Fahrenheit =
    Record["fahrenheit" of Float64]

  object Fahrenheit {
    def apply(value: Expr[Float64]): Expr[Fahrenheit] =
      Record.field("fahrenheit" -> value)
  }

  type Celsius =
    Record["celsius" of Float64]

  object Celsius {
    def apply(value: Expr[Float64]): Expr[Celsius] =
      Record.field("celsius" -> value)
  }

  type ConverterApi =
    Celsius --> Fahrenheit

  def start(host: String, port: Int)(using Runtime): ZIO[Scope, Throwable, Unit] =
    Service.runSimple(
      "TemperatureConverterService",
      Input.empty,
      Output.restApiAt(
        restApi,
        host,
        port,
      ),
      blueprint,
    )

  def restApi: RestApi[ConverterApi] =
    RestApi(endpoint)

  private def endpoint: Endpoint[Celsius, Fahrenheit] = {
    val p: RelativeUrl[Celsius] =
      path("c2f") / param[Float64] map (
        Celsius(_),
        { case "celsius" as value => value },
      )

    Endpoint.get(p)
  }

  def blueprint: Fun[EmptyResource, ConverterApi] =
    fun.? { _ =>
      closure { celsius =>
        celsius match {
          case "celsius" as value =>
            Fahrenheit(value * (9.0/5) + 32)
        }
      }
    }
}
