package libretto.mashup.examples

import org.scalatest.funsuite.AnyFunSuite

class AssemblyTests extends AnyFunSuite {
  test("weather") {
    weather.PragueWeatherService.blueprint
    weather.TemperatureConverterService.blueprint
    weather.WeatherService.blueprint
  }
}
