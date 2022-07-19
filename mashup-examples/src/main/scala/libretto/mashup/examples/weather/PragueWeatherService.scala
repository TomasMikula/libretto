package libretto.mashup.examples.weather

import libretto.mashup.{Input, Output, Runtime, Service}
import libretto.mashup.dsl.{|&|, ##, ###, -->, EmptyResource, Expr, Fun, Record, Unlimited, as, closure, fun, of}
import libretto.mashup.examples.weather.TemperatureConverterService.{ConverterApi, Fahrenheit}
import libretto.mashup.examples.weather.WeatherService.{Celsius, City, WeatherApi}
import libretto.mashup.rest.{Endpoint, RelativeUrl, RestApi}
import zio.{Scope, ZIO}

object PragueWeatherService {

  type PragueWeatherReport =
    Record["temperature" of Fahrenheit]

  type PragueWeatherApi =
    EmptyResource --> PragueWeatherReport

  def start(
    weatherService: Input[WeatherApi],
    temperatureConverter: Input[ConverterApi],
    host: String,
    port: Int,
  )(using
    runtime: Runtime,
  ): ZIO[Scope, Throwable, Unit] =
    Service.runStateless(
      input(weatherService, temperatureConverter),
      output(host, port),
      blueprint,
    )

  private type Inputs =
    (   ("weather"   of WeatherApi)
    |&| ("converter" of ConverterApi)
    )

  private def input(
    weatherService: Input[WeatherApi],
    temperatureConverter: Input[ConverterApi],
  ): Input[Inputs] =
    Input
      .choiceOf("weather", weatherService)
      .and     ("converter", temperatureConverter)

  private def output(host: String, port: Int): Output[PragueWeatherApi] =
    Output.restApiAt(restApi, host, port)

  private def restApi: RestApi[EmptyResource --> PragueWeatherReport] =
    RestApi(endpoint)

  private def endpoint: Endpoint[EmptyResource, PragueWeatherReport] =
    Endpoint.get(RelativeUrl.empty)

  private def blueprint: Fun[Unlimited[Inputs], PragueWeatherApi] =
    fun { inputs =>
      val (i1, i2) = inputs.split // manually duplicating because of linearity. TODO: infer splits automatically for Unlimited[A]
      val weather:   Expr[WeatherApi]   = i1.get.pick["weather"]
      val converter: Expr[ConverterApi] = i2.get.pick["converter"]
      closure { empty =>
        weather(City("Prague")) match {
          case ("city" as city) ### ("temperature" as celsius) =>
            val fahrenheit = converter(celsius)
            Record.field("temperature" -> fahrenheit)
              .alsoElim(empty)
        }
      }
    }
}
