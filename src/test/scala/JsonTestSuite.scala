package parrot

import org.scalatest.funsuite.AnyFunSuite

import java.nio.charset.{MalformedInputException, StandardCharsets}
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.{Failure, Success, Try}

/** Tests for the JSON grammar using the JSONTestSuite fixtures.
  *
  * The JSONTestSuite is a collection of test cases for JSON parsers, with files prefixed by:
  *   - `y_`: valid JSON files that should be accepted by the parser.
  *   - `n_`: invalid JSON files that should be rejected by the parser.
  *   - `i_`: implementation-defined files that may be accepted or rejected by the parser.
  */
class JsonTestSuite extends AnyFunSuite {
  import Parser.{run, given}

  private val exclude = List(
    "i_structure_500_nested_arrays.json",
    "n_structure_100000_opening_arrays.json",
    "n_structure_open_array_object.json",
    "n_structure_whitespace_formfeed.json",
  )
  private val grammar      = JsonGrammar[Parser]
  private val fixturesDir  = Path.of("src", "test", "resources", "json")
  private val fixtureNames = {
    if !Files.isDirectory(fixturesDir) then fail(s"Missing fixtures directory: $fixturesDir")
    val stream = Files.list(fixturesDir)
    try {
      stream.iterator().asScala
        .filter(path => Files.isRegularFile(path) && path.getFileName.toString.endsWith(".json"))
        .map(_.getFileName.toString)
        .filterNot(exclude.contains)
        .toList
        .sorted
    } finally stream.close()
  }

  private def expectationFor(fileName: String): Expectation = {
    if fileName.startsWith("y_") then Expectation.Accept
    else if fileName.startsWith("n_") then Expectation.Reject
    else if fileName.startsWith("i_") then Expectation.ImplementationDefined
    else fail(s"Unsupported JSONTestSuite fixture prefix: $fileName")
  }

  private def loadFixture(fileName: String): String = {
    val path   = fixturesDir.resolve(fileName)
    val stream = Files.newInputStream(path)
    val source = scala.io.Source.fromInputStream(stream, StandardCharsets.UTF_8.name())
    try source.mkString
    finally source.close()
  }

  private enum Expectation {
    case Accept, Reject, ImplementationDefined
  }

  for fileName <- fixtureNames do
    test(s"JSONTestSuite/$fileName") {
      val expectation = expectationFor(fileName)
      Try(loadFixture(fileName)) match {
        case Failure(_: MalformedInputException) if expectation != Expectation.Accept =>
          succeed
        case Failure(e) =>
          fail(e.getMessage)
        case Success(input) =>
          grammar.json.run(input) match {
            case Success((_, remaining)) if expectation == Expectation.Accept =>
              assert(remaining.isEmpty)
            case Failure(_) if expectation == Expectation.Reject =>
              succeed
            case Success((_, remaining)) if expectation == Expectation.Reject =>
              assert(remaining.nonEmpty)
            case Success((_, _)) if expectation == Expectation.ImplementationDefined =>
              succeed
            case Failure(_) if expectation == Expectation.ImplementationDefined =>
              succeed
            case Success((_, remaining)) =>
              fail(s"Expected full parse for $fileName, remaining='$remaining'")
            case Failure(e) =>
              fail(e.getMessage)
          }
      }
    }
}
