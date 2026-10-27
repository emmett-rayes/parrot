package parrot
package json

import org.scalatest.funsuite.AnyFunSuite

/** Both interpreters on the JSON test sets of [[JsonFixtures]]: every document of `json-test-suite` and the
  * JSON_checker documents of `nativejson-benchmark`, parsed with the stack of [[JsonFixtures.onDeepStack]].
  */
class JsonCorporaTest extends AnyFunSuite {
  import JsonBenchmark.Interpreter

  private val interpreters = List(JsonBenchmark.reference, JsonBenchmark.strict)

  /** Whether `interpreter` accepts `name` from `suite`; a document that is not valid UTF-8 is rejected. */
  private def accepts(interpreter: Interpreter, suite: String, name: String): Boolean = {
    JsonFixtures.load(suite, name).toOption.exists(input => JsonFixtures.onDeepStack(() => interpreter.accepts(input)))
  }

  /** The documents of `suite` that `interpreter` does not judge as `expected`. */
  private def misjudged(
    interpreter: Interpreter,
    suite: String,
    names: List[String],
    expected: Boolean
  ): List[String] = {
    names.filterNot(name => accepts(interpreter, suite, name) == expected)
  }

  private val testSuite = JsonFixtures.jsonTestSuite

  for interpreter <- interpreters do {

    test(s"${interpreter.name} accepts every valid document of JSONTestSuite (y_)") {
      assert(misjudged(
        interpreter,
        JsonFixtures.jsonTestSuiteSuite,
        testSuite.filter(_.startsWith("y_")),
        true
      ).isEmpty)
    }

    test(s"${interpreter.name} rejects every invalid document of JSONTestSuite (n_)") {
      assert(misjudged(
        interpreter,
        JsonFixtures.jsonTestSuiteSuite,
        testSuite.filter(_.startsWith("n_")),
        false
      ).isEmpty)
    }

    test(s"${interpreter.name} passes JSON_checker: pass*.json accepted, fail*.json rejected") {
      val suite = JsonFixtures.nativeJsonBenchmarkSuite
      val pass  = (1 to 3).map(i => f"jsonchecker/pass$i%02d.json").toList
      val fail  = (2 to 33).filterNot(_ == 18).map(i => f"jsonchecker/fail$i%02d.json").toList
      val _     = assert(misjudged(interpreter, suite, pass, true).isEmpty)
      assert(misjudged(interpreter, suite, fail, false).isEmpty)
    }
  }

  test("the interpreters agree on the implementation-defined documents of JSONTestSuite (i_)") {
    val suite     = JsonFixtures.jsonTestSuiteSuite
    val disagreed = testSuite.filter(_.startsWith("i_")).filterNot { name =>
      accepts(JsonBenchmark.reference, suite, name) == accepts(JsonBenchmark.strict, suite, name)
    }
    assert(disagreed.isEmpty)
  }
}
