package libretto.mashup.examples.weather

import libretto.mashup.{Input, Output, Runtime, Service}
import libretto.mashup.dsl.{-->, ##, EmptyResource, Float64, Fun, Record, closure, fun, of}
import libretto.mashup.rest.RestApi
import zio.{Scope, ZIO}

object TemperatureConverterService {
  type Fahrenheit =
    Record["fahrenheit" of Float64]

  type Celsius =
    Record["celsius" of Float64]

  type ConverterApi =
    Celsius --> Fahrenheit

  def start(host: String, port: Int)(using Runtime): ZIO[Scope, Throwable, Unit] =
    Service.runStateless(
      Input.empty,
      Output.restApiAt(
        restApi,
        host,
        port,
      ),
      blueprint,
    )

  private def restApi: RestApi[ConverterApi] =
    throw NotImplementedError("TemperatureConverterService.restApi")

  private def blueprint: Fun[EmptyResource, ConverterApi] =
    fun { emptyResource =>
      closure { celsius =>
        ???
      }
    }
}
