package libretto.mashup.examples.weather

import libretto.mashup.{Input, Output, Runtime, Service}
import libretto.mashup.dsl.{|&|, ###, -->, EmptyResource, Expr, Fun, Record, Unlimited, as, closure, fun, of}
import libretto.mashup.examples.weather.TemperatureConverterService.{ConverterApi, Fahrenheit}
import libretto.mashup.examples.weather.WeatherService.{City, WeatherApi}
import libretto.mashup.rest.{Endpoint, RelativeUrl, RestApi}
import zio.{Scope, ZIO}

/** A service providing current temperature in Fahrenheits in Prague.
 *  To do its job, it uses two other services:
 *   - a service that provides weather for any city in Celsius;
 *   - a service that converts Celsius to Fahrenheit.
 *
 *  See [[Main]] for instructions to run.
 */
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
  ): ZIO[Scope, Throwable, Unit] = {
    // To start a service, we need to provide *descriptions* of
    //  - inputs (addresses and interfaces of dependencies)
    //  - output (address and interface of this service)
    //  - business logic.
    //
    // All of these are *pure values* without embedded Scala functions.
    //
    // Input and output descriptions could possibly be generated
    // from OpenAPI spec or similar.
    Service.runStateless(
      input(weatherService, temperatureConverter),
      output(host, port),
      blueprint,
    )
  }

  /** Type of inputs to this service: weather API and temperature converter API. */
  private type Inputs =
    (   ("weather"   of WeatherApi)
    |&| ("converter" of ConverterApi)
    )

  /** Declarative description of this service's inputs (dependencies). */
  private def input(
    weatherService: Input[WeatherApi],
    temperatureConverter: Input[ConverterApi],
  ): Input[Inputs] =
    Input
      .choiceOf("weather", weatherService)
      .and     ("converter", temperatureConverter)

  /** Declarative description of the output of this service. */
  private def output(host: String, port: Int): Output[PragueWeatherApi] =
    Output.restApiAt(
      RestApi(Endpoint.get(RelativeUrl.empty)),
      host,
      port,
    )

  /** Defines the business logic: how to resolve a request for Prague weather
   *  using (unlimited access to) two other APIs (general weather API and
   *  temperature converter API).
   *
   *  Note that the resulting `Fun` is just a data structure
   *  without any Scala functions inside.
   */
  private def blueprint: Fun[Unlimited[Inputs], PragueWeatherApi] =
    fun.* { inputs =>
      // from the inputs, get one WeatherApi and one ConverterApi
      val weather:   Expr[WeatherApi]   = inputs.get.pick["weather"]
      val converter: Expr[ConverterApi] = inputs.get.pick["converter"]

      closure.? { empty =>
        // invoke the weather API, passing in `City("Prague")` as the argument
        weather(City("Prague")) match {
          // deconstruct the response
          case ("city" as city) ### ("temperature" as celsius) =>
            // invoke the converter API to convert Celsius to Fahrenheit
            val fahrenheit = converter(celsius)

            // form the response
            Record.field("temperature" -> fahrenheit)
              .alsoAwait(city) // XXX: Can't simply ignore stuff due to linearity.
                               // Will be ameliorated by dedicated support for *value* types.
        }
      }
    }
}
