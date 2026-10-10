package parrot
package parser

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** The JSON fixtures in `src/test/resources/json`, from two sources:
  *   - [[jsonTestSuite]]: the `test_parsing` documents of JSONTestSuite, [[https://github.com/nst/JSONTestSuite]] at
  *     commit `1ef36fa` (MIT license)
  *   - [[jsonDummyData]]: the `y_sample_*` documents of [[https://microsoftedge.github.io/Demos/json-dummy-data]]
  *
  * The fixtures are prefixed by
  *   - `y_`: valid JSON that must be accepted
  *   - `n_`: invalid JSON that must be rejected
  *   - `i_`: implementation-defined JSON that may be accepted or rejected
  */
object JsonFixtures {

  val directory: Path = Path.of("src", "test", "resources", "json")

  /** Nesting too deep for the call stack. */
  val excluded: Set[String] = Set(
    "i_structure_500_nested_arrays.json",
    "n_structure_100000_opening_arrays.json",
    "n_structure_open_array_object.json",
  )

  /** True if `name` is one of the json-dummy-data documents rather than a JSONTestSuite fixture. */
  def isDummyData(name: String): Boolean = name.startsWith("y_sample_")

  /** The JSONTestSuite fixtures that are not [[excluded]], sorted. */
  def jsonTestSuite: List[String] = names.filterNot(isDummyData)

  /** The json-dummy-data documents, sorted. */
  def jsonDummyData: List[String] = names.filter(isDummyData)

  /** The names of the fixtures that are not [[excluded]], sorted. */
  def names: List[String] = {
    val stream = Files.list(directory)
    try {
      stream.iterator().asScala
        .map(_.getFileName.toString)
        .filter(name => name.endsWith(".json") && !excluded.contains(name))
        .toList
        .sorted
    } finally stream.close()
  }

  /** The raw bytes of a fixture. */
  def bytes(name: String): Array[Byte] = Files.readAllBytes(directory.resolve(name)).nn

  /** The content of a fixture, failing with a `MalformedInputException` if it is not valid UTF-8. */
  def load(name: String): Try[String] = Try {
    StandardCharsets.UTF_8.newDecoder().decode(java.nio.ByteBuffer.wrap(bytes(name))).toString
  }
}
