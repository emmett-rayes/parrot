package parrot
package parser

import java.nio.file.{Files, Path}

/** Compares the throughput of the interpreters on the JSON grammar.
  *
  * Run with `sbt "Test/runMain parrot.parser.JsonBenchmark [fixture.json ...]"`.
  */
object JsonBenchmark {

  /** A named way to parse a whole JSON document, returning whether it was accepted. */
  final case class Interpreter(name: String, accepts: String => Boolean)

  def reference: Interpreter = {
    val grammar = JsonGrammar(ReferenceParser)
    Interpreter(
      "ReferenceParser",
      input =>
        ReferenceParser.parse(grammar.json)(input) match {
          case ReferenceParser.Result.Success(_, offset) => offset == input.length
          case ReferenceParser.Result.Failure(_, _)      => false
        },
    )
  }

  def strict: Interpreter = {
    val grammar = JsonGrammar(StrictParser)
    Interpreter("StrictParser", input => StrictParser.parse(grammar.json)(input).exists(_.offset == input.length))
  }

  val defaultFixtures: List[String] = List("y_sample_1_mb.json", "y_sample_5_mb.json", "y_sample_5120_kb_min.json")

  /** Times each interpreter on each fixture: the median of `runs` runs after `warmup` runs. */
  def run(interpreters: List[Interpreter], fixtures: List[String], warmup: Int = 3, runs: Int = 7): Unit = {
    for fixture <- fixtures do {
      val input = Files.readString(Path.of("src", "test", "resources", "json", fixture)).nn
      val mb    = input.length / 1e6
      println(f"$fixture (${mb}%.2f M chars)")
      for interpreter <- interpreters do {
        val result = scala.util.Try {
          for _ <- 1 to warmup do require(interpreter.accepts(input), "rejected")
          val times = (1 to runs).map { _ =>
            val start = System.nanoTime()
            val _     = interpreter.accepts(input)
            (System.nanoTime() - start) / 1e6
          }.sorted
          times(runs / 2)
        }
        result match {
          case scala.util.Success(ms) =>
            println(f"  ${interpreter.name}%-24s ${ms}%9.1f ms ${mb / ms * 1000}%8.1f M chars/s")
          case scala.util.Failure(e) => println(f"  ${interpreter.name}%-24s failed: ${e.getClass.getSimpleName}")
        }
      }
    }
  }

  def main(args: Array[String]): Unit = {
    run(List(reference, strict), if args.isEmpty then defaultFixtures else args.toList)
  }
}
