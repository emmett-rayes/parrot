package parrot
package parser

/** Compares the throughput of the interpreters on the JSON grammar over the whole [[JsonFixtures]] suite.
  *
  * Run with `sbt "Test/runMain parrot.parser.JsonBenchmark [fixture.json ...]"`; without arguments, every fixture that
  * is valid UTF-8 is parsed. Throughput is measured in megabytes of UTF-8 input per second, per group of fixtures and
  * in total, from the median of several passes over each group.
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

  /** A decoded fixture and its size in bytes. */
  final case class Fixture(name: String, input: String, bytes: Int)

  /** A group of fixtures, measured together. */
  final case class Group(label: String, fixtures: List[Fixture]) {
    val megabytes: Double = fixtures.map(_.bytes).sum / 1e6
  }

  /** The fixtures `names` that are valid UTF-8, grouped by expectation. */
  def groups(names: List[String]): List[Group] = {
    val fixtures = names.flatMap { name =>
      JsonFixtures.load(name).toOption.map(Fixture(name, _, JsonFixtures.bytes(name).length))
    }
    List("valid (y_)" -> "y_", "invalid (n_)" -> "n_", "implementation-defined (i_)" -> "i_")
      .map((label, prefix) => Group(label, fixtures.filter(_.name.startsWith(prefix))))
      .filter(_.fixtures.nonEmpty)
  }

  /** The median duration in milliseconds of `runs` passes of `interpreter` over `group`, after `warmup` passes, and the
    * number of fixtures it accepts.
    */
  def measure(interpreter: Interpreter, group: Group, warmup: Int, runs: Int): (ms: Double, accepted: Int) = {
    def pass(): Int = group.fixtures.count(fixture => interpreter.accepts(fixture.input))
    for _ <- 1 to warmup do {
      val _ = pass()
    }
    var accepted = 0
    val times    = (1 to runs).map { _ =>
      val start = System.nanoTime()
      accepted = pass()
      (System.nanoTime() - start) / 1e6
    }.sorted
    (ms = times(runs / 2), accepted = accepted)
  }

  /** Measures each interpreter on each group, then compares the total throughputs with that of the first one. */
  def run(interpreters: List[Interpreter], names: List[String], warmup: Int = 3, runs: Int = 7): Unit = {
    val suite = groups(names)
    val total = suite.map(_.megabytes).sum
    println(f"${suite.map(_.fixtures.size).sum} fixtures, $total%.2f MB, median of $runs passes after $warmup warm-ups")
    val throughputs =
      for interpreter <- interpreters yield {
        println(interpreter.name)
        val ms = suite.map { group =>
          val result = measure(interpreter, group, warmup, runs)
          println(
            f"  ${group.label}%-28s ${group.fixtures.size}%4d fixtures ${result.accepted}%4d accepted " +
              f"${group.megabytes}%9.4f MB ${result.ms}%9.1f ms ${group.megabytes / result.ms * 1000}%8.1f MB/s"
          )
          result.ms
        }.sum
        val throughput = total / ms * 1000
        println(f"  ${"total"}%-58s ${total}%9.4f MB ${ms}%9.1f ms ${throughput}%8.1f MB/s")
        throughput
      }
    for (interpreter, throughput) <- interpreters.zip(throughputs).drop(1) do {
      println(f"${interpreter.name}: ${throughput / throughputs.head}%.1fx the throughput of ${interpreters.head.name}")
    }
  }

  def main(args: Array[String]): Unit = {
    run(List(reference, strict), if args.isEmpty then JsonFixtures.names else args.toList)
  }
}
