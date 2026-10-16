package parrot
package json

import java.nio.ByteBuffer
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.jdk.CollectionConverters.*
import scala.util.Try

/** The JSON test sets in `src/test/resources/json`, each in its own folder:
  *   - `json-test-suite`: the `test_parsing` documents of [[https://github.com/nst/JSONTestSuite]] at commit `1ef36fa`
  *   - `json-dummy-data`: the sample documents of [[https://microsoftedge.github.io/Demos/json-dummy-data]]
  *   - `json-benchmark`: the sample documents of [[https://github.com/TkTech/json_benchmark]] at commit `52d596b`
  *   - `nativejson-benchmark`: the benchmark and `JSON_checker` documents of
  *     [[https://github.com/miloyip/nativejson-benchmark]] at commit `478d572`
  */
object JsonFixtures {

  val directory: Path = Path.of("src", "test", "resources", "json").nn

  val jsonTestSuiteSuite: String       = "json-test-suite"
  val jsonDummyDataSuite: String       = "json-dummy-data"
  val jsonBenchmarkSuite: String       = "json-benchmark"
  val nativeJsonBenchmarkSuite: String = "nativejson-benchmark"

  /** Nesting too deep for the call stack. */
  val excluded: Set[String] = Set(
    "i_structure_500_nested_arrays.json",
    "n_structure_100000_opening_arrays.json",
    "n_structure_open_array_object.json",
  )

  /** The `.json` file names directly inside `suite`, sorted. */
  def namesIn(suite: String): List[String] = {
    val stream = Files.list(directory.resolve(suite)).nn
    try {
      stream.iterator().nn.asScala
        .map(_.getFileName.nn.toString)
        .filter(_.endsWith(".json"))
        .toList
        .sorted
    } finally stream.close()
  }

  /** The `json-test-suite` fixtures that are not [[excluded]], sorted. */
  def jsonTestSuite: List[String] = {
    namesIn(jsonTestSuiteSuite).filterNot(excluded.contains)
  }

  /** The `json-dummy-data` documents, sorted. */
  def jsonDummyData: List[String] = {
    namesIn(jsonDummyDataSuite)
  }

  /** The raw bytes of `path` inside `suite`. */
  def bytes(suite: String, path: String): Array[Byte] = {
    Files.readAllBytes(directory.resolve(suite).nn.resolve(path)).nn
  }

  /** The UTF-8 content of `path` inside `suite`, failing with a `MalformedInputException` if it is not valid UTF-8. */
  def load(suite: String, path: String): Try[String] = Try {
    StandardCharsets.UTF_8.nn.newDecoder().nn.decode(ByteBuffer.wrap(bytes(suite, path))).nn.toString
  }
}
