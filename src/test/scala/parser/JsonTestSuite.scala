package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.{MalformedInputException, StandardCharsets}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.{Failure, Success, Try}

/** Runs the JSON grammar on the JSONTestSuite fixtures (ported from the legacy interpreter), on both interpreters.
  *
  * The fixtures are prefixed by
  *   - `y_`: valid JSON that must be accepted
  *   - `n_`: invalid JSON that must be rejected
  *   - `i_`: implementation-defined JSON that may be accepted or rejected
  *
  * Whatever the expectation, both interpreters must agree on the result.
  */
class JsonTestSuite extends AnyFunSuite {

  given CanEqual[Any, Any] = CanEqual.derived

  /** Nesting too deep for the call stack, and a fixture whose form feed was lost (it contains `[]`). */
  private val exclude = List(
    "i_structure_500_nested_arrays.json",
    "n_structure_100000_opening_arrays.json",
    "n_structure_open_array_object.json",
    "n_structure_whitespace_formfeed.json",
  )

  private val reference = JsonGrammar(ReferenceParser)
  private val strict    = JsonGrammar(StrictParser)

  private val fixturesDir  = Path.of("src", "test", "resources", "json")
  private val fixtureNames = {
    val stream = Files.list(fixturesDir)
    try {
      stream.iterator().asScala
        .map(_.getFileName.toString)
        .filter(_.endsWith(".json"))
        .filterNot(exclude.contains)
        .toList
        .sorted
    } finally stream.close()
  }

  private def load(fileName: String): Try[String] = Try {
    val decoder = StandardCharsets.UTF_8.newDecoder()
    decoder.decode(java.nio.ByteBuffer.wrap(Files.readAllBytes(fixturesDir.resolve(fileName)))).toString
  }

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

  for fileName <- fixtureNames do
    test(s"JSONTestSuite/$fileName") {
      load(fileName) match {
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
