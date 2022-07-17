package libretto.mashup.examples.weather

import libretto.mashup.{Input, Output, Runtime, Service}
import libretto.mashup.dsl.{|&|, ##, -->, EmptyResource, Fun, NamedChoice, of}
import libretto.mashup.examples.weather.TemperatureConverterService.{ConverterApi, Fahrenheit}
import libretto.mashup.examples.weather.WeatherService.{Celsius, WeatherApi}
import zio.{Scope, ZIO}

object PragueWeatherService {

  type PragueWeatherReport =
    Record ## ("temperature" of Fahrenheit)

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
    throw NotImplementedError("PragueWeatherService.output")

  private def blueprint: Fun[Inputs, PragueWeatherApi] =
    throw NotImplementedError("PragueWeatherService.blueprint")
}
