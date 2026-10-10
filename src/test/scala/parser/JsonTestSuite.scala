package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.MalformedInputException
import scala.util.{Failure, Success}

/** Runs the JSON grammar on the [[JsonFixtures]] (ported from the legacy interpreter), on both interpreters.
  *
  * Valid (`y_`) fixtures must be accepted and invalid (`n_`) ones rejected. Whatever the expectation, both interpreters
  * must agree on the result.
  */
class JsonTestSuite extends AnyFunSuite {

  given CanEqual[Any, Any] = CanEqual.derived

  private val reference = JsonGrammar(ReferenceParser)
  private val strict    = JsonGrammar(StrictParser)

  /** Parses `input` on a prefix, returning the result and whether the whole input was consumed. */
  private def runReference(input: String): Option[(JsonGrammar.JsonJson, Boolean)] = {
    ReferenceParser.parse(reference.json)(input) match {
      case ReferenceParser.Result.Success(value, offset) => Some((value, offset == input.length))
      case ReferenceParser.Result.Failure(_, _)          => None
    }
  }

  private def runStrict(input: String): Option[(JsonGrammar.JsonJson, Boolean)] = {
    StrictParser.parse(strict.json)(input).toOption.map(r => (r.value, r.offset == input.length))
  }

  for fileName <- JsonFixtures.names do
    test(s"JSONTestSuite/$fileName") {
      JsonFixtures.load(fileName) match {
        case Failure(_: MalformedInputException) => val _ = assert(!fileName.startsWith("y_"))
        case Failure(e)                          => fail(e)
        case Success(input)                      =>
          val strictResult = runStrict(input)
          val accepted     = strictResult.exists(_._2)
          if fileName.startsWith("y_") then {
            val _ = assert(accepted, "valid JSON rejected")
          } else if fileName.startsWith("n_") then {
            val _ = assert(!accepted, "invalid JSON accepted")
          }
          val _ = assert(runReference(input) == strictResult, "interpreters disagree")
      }
    }
}
