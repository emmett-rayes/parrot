package parrot
package json

import parser.{ReferenceParser, StrictParser}

import java.lang.management.ManagementFactory
import java.nio.file.Path
import scala.annotation.tailrec
import scala.jdk.CollectionConverters.*

/** Compares the throughput and memory usage of the interpreters on [[JsonGrammar]], with the four test sets of
  * [[JsonFixtures]], run one after the other and reported separately:
  *   - `json-test-suite`: grouped by expectation
  *   - `json-dummy-data`: document by document
  *   - `json-benchmark`: with the methodology of its upstream benchmark
  *   - `nativejson-benchmark`: its Parse and Parse Validation benchmarks, with their methodology
  *
  * Run with `sbt "Test/runMain parrot.json.JsonBenchmark [--reference] [suite ...]"`; without suites, all suites run.
  * Only [[StrictParser]] is measured unless `--reference` adds [[ReferenceParser]] as the baseline it is compared with;
  * the reference interpreter is slow on the large documents of `json-benchmark`.
  *
  * Memory is the number of bytes allocated on the heap by the parsing thread, also per byte of input, and the time
  * spent in garbage collection during the measured runs. Garbage is collected before each measured run, so that runs do
  * not pay for the garbage of earlier ones.
  */
object JsonBenchmark {

  /** A named way to parse a whole JSON document, returning whether it was accepted. */
  final case class Interpreter(name: String, accepts: String -> Boolean)

  /** The [[ReferenceParser]] interpreter on [[JsonGrammar]]. */
  def reference: Interpreter = {
    val parser  = ReferenceParser()
    val grammar = JsonGrammar(parser)
    Interpreter(
      "ReferenceParser",
      input => parser.parse(grammar.json)(input).toOption.exists(_.offset == input.length),
    )
  }

  /** The [[StrictParser]] interpreter on [[JsonGrammar]]. */
  def strict: Interpreter = {
    val parser  = StrictParser()
    val grammar = JsonGrammar(parser)
    Interpreter(
      "StrictParser",
      input => parser.parse(grammar.json)(input).toOption.exists(_.offset == input.length),
    )
  }

  /** A decoded document and its size in bytes. */
  final case class Fixture(name: String, input: String, bytes: Int)

  /** Loads `path` from `suite` in [[JsonFixtures]]. */
  private def loadFixture(suite: String, path: String): Fixture = {
    val raw   = JsonFixtures.bytes(suite, path)
    val input = JsonFixtures.load(suite, path).get
    val name  = Path.of(path).nn.getFileName.nn.toString
    Fixture(name, input, raw.length)
  }

  /** The bytes allocated so far by the current thread. */
  private def allocatedBytes(): Long = {
    ManagementFactory.getThreadMXBean match {
      case threads: com.sun.management.ThreadMXBean => threads.getCurrentThreadAllocatedBytes
      case _                                        => throw UnsupportedOperationException("allocation counters")
    }
  }

  /** The time spent in garbage collection so far, in milliseconds. */
  private def gcMillis(): Long = {
    ManagementFactory.getGarbageCollectorMXBeans.nn.asScala.map(_.getCollectionTime.max(0L)).sum
  }

  /** One measured run: its duration and allocation, per unit of work. */
  final case class Sample(ms: Double, allocated: Double)

  /** The samples of the measured runs, the time spent in garbage collection during them, and the result of the work. */
  final case class Measurement(samples: IndexedSeq[Sample], gcMs: Long, accepted: Int) {
    private val times = samples.map(_.ms).sorted

    def min: Double    = times.head
    def max: Double    = times.last
    def mean: Double   = times.sum / times.size
    def median: Double = times(times.size / 2)

    def allocated: Double = samples.map(_.allocated).sorted.apply(samples.size / 2)
  }

  /** Collects garbage until the used heap stops shrinking, so that the next run does not pay for the garbage of earlier
    * ones (runs, documents or interpreters).
    */
  private def collectGarbage(): Unit = {
    val memory = ManagementFactory.getMemoryMXBean.nn

    @tailrec
    def loop(used: Long, rounds: Int): Unit = {
      val current = memory.getHeapMemoryUsage.nn.getUsed
      if rounds < 5 && current < used then {
        System.gc()
        loop(current, rounds + 1)
      }
    }

    loop(Long.MaxValue, 0)
  }

  /** Measures `runs` runs of `work` after `warmup` runs. Each run repeats `work` until it takes at least `minRunMs`, so
    * that small documents are timed reliably, and samples are reported per repetition.
    *
    * Garbage is collected before each run, outside of the measurement, so that the garbage collection time of a run
    * (counted in [[Measurement.gcMs]]) is only due to its own allocations.
    */
  def measure(work: () => Int, warmup: Int, runs: Int, minRunMs: Double = 0): Measurement = {
    val warmupRuns = (1 to warmup.max(1)).map { _ =>
      val start = System.nanoTime()
      val res   = work()
      (res, (System.nanoTime() - start) / 1e6)
    }
    val slowest     = warmupRuns.map(_._2).max
    val repetitions = if slowest >= minRunMs then 1 else math.ceil(minRunMs / slowest.max(1e-3)).toInt
    val measured    = (1 to runs).map { _ =>
      collectGarbage()
      val gcBefore = gcMillis()
      val bytes    = allocatedBytes()
      val start    = System.nanoTime()
      val accepted = (1 to repetitions).foldLeft(0)((_, _) => work())
      val ms       = (System.nanoTime() - start) / 1e6
      val gcDelta  = gcMillis() - gcBefore
      (Sample(ms / repetitions, (allocatedBytes() - bytes).toDouble / repetitions), gcDelta, accepted)
    }
    Measurement(measured.map(_._1), measured.map(_._2).sum, measured.lastOption.fold(warmupRuns.last._1)(_._3))
  }

  private def megabytes(bytes: Double): Double = bytes / 1e6

  private def heading(title: String): Unit = println(s"\n=== $title ===")

  /** A column of a [[Table]], `left`- or right-aligned. */
  final private case class Column(header: String, width: Int, left: Boolean = false)

  /** A text table, printed row by row after a header. */
  final private class Table(columns: Column*) {
    private val widths = columns.map(column => column.width.max(column.header.length))

    private def line(cells: Seq[String]): String = {
      cells.zip(columns).zip(widths).map { case ((cell, column), width) =>
        if column.left then cell.padTo(width, ' ') else " " * (width - cell.length) + cell
      }.mkString("  ", "  ", "").stripTrailing
    }

    def header(): Unit = {
      println(line(columns.map(_.header)))
      println(line(widths.map("-" * _)))
    }

    def row(cells: String*): Unit = println(line(cells))
  }

  private def decimal(x: Double, digits: Int): String = s"%.${digits}f".format(x)

  /** A human-readable size in decimal units, as for the throughputs. */
  private def size(bytes: Long): String = {
    if bytes < 1000 then s"$bytes B"
    else if bytes < 1000 * 1000 then s"${decimal(bytes / 1e3, 1)} kB"
    else s"${decimal(bytes / 1e6, 1)} MB"
  }

  /** A group of fixtures, measured together. */
  final case class Group(label: String, fixtures: List[Fixture]) {
    val bytes: Long = fixtures.map(_.bytes.toLong).sum
  }

  /** The `json-test-suite` fixtures in [[JsonFixtures]] that are valid UTF-8, grouped by expectation. */
  def groups(names: List[String]): List[Group] = {
    val suite    = JsonFixtures.jsonTestSuiteSuite
    val fixtures = names.flatMap { name =>
      JsonFixtures.load(suite, name).toOption.map(Fixture(name, _, JsonFixtures.bytes(suite, name).length))
    }
    List("valid (y_)" -> "y_", "invalid (n_)" -> "n_", "implementation-defined (i_)" -> "i_")
      .map((label, prefix) => Group(label, fixtures.filter(_.name.startsWith(prefix))))
      .filter(_.fixtures.nonEmpty)
  }

  private val groupTable = Table(
    Column("interpreter", 16, left = true),
    Column("group", 27, left = true),
    Column("fixtures", 8),
    Column("accepted", 8),
    Column("size", 8),
    Column("time ms", 9),
    Column("MB/s", 7),
    Column("alloc MB", 9),
    Column("alloc B/B", 9),
    Column("GC ms", 6),
  )

  private def reportGroup(
    interpreter: Interpreter,
    label: String,
    fixtures: Int,
    accepted: Int,
    bytes: Long,
    ms: Double,
    allocated: Double,
    gcMs: Long,
  ): Unit = {
    groupTable.row(
      interpreter.name,
      label,
      fixtures.toString,
      accepted.toString,
      size(bytes),
      decimal(ms, 3),
      decimal(megabytes(bytes.toDouble) / ms * 1000, 1),
      decimal(megabytes(allocated), 1),
      decimal(allocated / bytes, 1),
      gcMs.toString,
    )
  }

  /** Parses each group in passes, and reports the medians per pass, per group and in total. */
  def runJsonTestSuite(
    interpreters: List[Interpreter],
    warmup: Int = 3,
    runs: Int = 7,
    minRunMs: Double = 100,
  ): Unit = {
    val suite = groups(JsonFixtures.jsonTestSuite)
    val bytes = suite.map(_.bytes).sum
    heading("json-test-suite (github.com/nst/JSONTestSuite@1ef36fa, test_parsing)")
    println(
      s"${suite.map(_.fixtures.size).sum} fixtures, ${size(bytes)}: " +
        s"median of $runs runs after $warmup warm-ups, per pass over the fixtures " +
        s"(runs repeat passes to at least ${minRunMs.toInt} ms; alloc: heap bytes allocated per pass)"
    )
    groupTable.header()
    val totals =
      for interpreter <- interpreters yield {
        val measurements = suite.map { group =>
          val pass = () => group.fixtures.count(fixture => interpreter.accepts(fixture.input))
          val m    = measure(pass, warmup, runs, minRunMs)
          val size = group.fixtures.size
          reportGroup(interpreter, group.label, size, m.accepted, group.bytes, m.median, m.allocated, m.gcMs)
          m
        }
        val (ms, allocated) = (measurements.map(_.median).sum, measurements.map(_.allocated).sum)
        val fixtures        = suite.map(_.fixtures.size).sum
        val accepted        = measurements.map(_.accepted).sum
        reportGroup(interpreter, "total", fixtures, accepted, bytes, ms, allocated, measurements.map(_.gcMs).sum)
        (ms, allocated)
      }
    compare(interpreters, totals)
  }

  /** Compares the totals (time, allocation) of each interpreter with those of the first. */
  private def compare(interpreters: List[Interpreter], totals: List[(Double, Double)]): Unit = {
    for (interpreter, (ms, allocated)) <- interpreters.zip(totals).drop(1) do {
      val (baselineMs, baselineAllocated) = totals.head
      println(
        f"${interpreter.name}: ${baselineMs / ms}%.1fx the throughput and " +
          f"${allocated / baselineAllocated}%.2fx the allocation of ${interpreters.head.name}"
      )
    }
  }

  /** [[https://github.com/TkTech/json_benchmark]]: complete loads of each sample document, reported per document by the
    * minimum, maximum and mean duration, as by `pytest-benchmark`.
    */
  object TkTech {

    /** The `SAMPLE_FILES` of `tests/conftest.py`, in order. */
    val samples: List[String] = List(
      "canada.json",
      "citm_catalog.json",
      "twitter.json",
      "verysmall.json",
      "fgo.json",
      "otfcc.json",
      "poet.json",
      "gsoc-2018.json",
    )

    val suite: String  = JsonFixtures.jsonBenchmarkSuite
    val source: String = "github.com/TkTech/json_benchmark@52d596b"

    def run(interpreters: List[Interpreter], warmup: Int = 1, runs: Int = 5, minRunMs: Double = 100): Unit = {
      heading(s"json-benchmark ($source)")
      println(
        s"complete load of each document: min, max and mean of $runs runs after $warmup warm-up, per load " +
          s"(runs repeat loads to at least ${minRunMs.toInt} ms; alloc: heap bytes allocated per load)"
      )
      val table = documentTable(samples)
      table.header()
      for path <- samples do {
        loadEach(table, interpreters, path, loadFixture(suite, path), warmup, runs, minRunMs)
      }
    }
  }

  /** The table of the `documents` of a suite. */
  private def documentTable(documents: List[String]): Table = Table(
    Column("document", documents.map(_.length).max, left = true),
    Column("size", 8),
    Column("interpreter", 16, left = true),
    Column("min ms", 11),
    Column("max ms", 11),
    Column("mean ms", 11),
    Column("MB/s", 7),
    Column("alloc MB", 9),
    Column("alloc B/B", 9),
    Column("GC ms", 6),
    Column("accepted", 8),
  )

  /** Measures each interpreter on `document`, reporting the minimum, maximum and mean duration per load. */
  private def loadEach(
    table: Table,
    interpreters: List[Interpreter],
    title: String,
    document: Fixture,
    warmup: Int,
    runs: Int,
    minRunMs: Double,
  ): Unit = {
    for interpreter <- interpreters do {
      val m = measure(() => if interpreter.accepts(document.input) then 1 else 0, warmup, runs, minRunMs)
      table.row(
        title,
        size(document.bytes.toLong),
        interpreter.name,
        decimal(m.min, 4),
        decimal(m.max, 4),
        decimal(m.mean, 4),
        decimal(megabytes(document.bytes.toDouble) / m.mean * 1000, 1),
        decimal(megabytes(m.allocated), 2),
        decimal(m.allocated / document.bytes, 1),
        m.gcMs.toString,
        if m.accepted == 1 then "yes" else "NO",
      )
    }
  }

  /** The documents of [[https://microsoftedge.github.io/Demos/json-dummy-data]], vendored in [[JsonFixtures]], loaded
    * one by one and reported like `json-benchmark`.
    */
  def runJsonDummyData(
    interpreters: List[Interpreter],
    warmup: Int = 3,
    runs: Int = 7,
    minRunMs: Double = 100,
  ): Unit = {
    heading("json-dummy-data (microsoftedge.github.io/Demos/json-dummy-data)")
    println(
      s"load of each document: min, max and mean of $runs runs after $warmup warm-ups, per load " +
        s"(runs repeat loads to at least ${minRunMs.toInt} ms; alloc: heap bytes allocated per load)"
    )
    val names = JsonFixtures.jsonDummyData
    val table = documentTable(names)
    table.header()
    for name <- names do {
      val document = loadFixture(JsonFixtures.jsonDummyDataSuite, name)
      loadEach(table, interpreters, name, document, warmup, runs, minRunMs)
    }
  }

  /** [[https://github.com/miloyip/nativejson-benchmark]]:
    *   - Parse Validation: the JSON_checker documents `pass*.json` must be accepted and `fail*.json` rejected, except
    *     `fail01.json` (relaxed by RFC 7159) and `fail18.json` (nesting depth is unspecified)
    *   - Parse: each document is parsed in 10 trials, reported by the minimum duration and the throughput in MiB/s, per
    *     document and as the total over the documents
    */
  object NativeJson {

    /** `data/data.txt`. */
    val documents: List[String] = List("canada.json", "citm_catalog.json", "twitter.json")

    val pass: List[String] = (1 to 3).map(i => f"jsonchecker/pass$i%02d.json").toList

    val fail: List[String] = (2 to 33).filterNot(_ == 18).map(i => f"jsonchecker/fail$i%02d.json").toList

    val suite: String  = JsonFixtures.nativeJsonBenchmarkSuite
    val source: String = "github.com/miloyip/nativejson-benchmark@478d572"

    val trials = 10

    def run(interpreters: List[Interpreter], warmup: Int = 3, minRunMs: Double = 100): Unit = {
      heading(s"nativejson-benchmark ($source)")

      println("Parse Validation (JSON_checker): pass*.json accepted, fail*.json rejected")
      val validation =
        pass.map(loadFixture(suite, _) -> true) ++ fail.map(loadFixture(suite, _) -> false)
      validationTable.header()
      for interpreter <- interpreters do {
        val wrong = validation.collect {
          case (document, valid) if interpreter.accepts(document.input) != valid => document.name
        }
        val correct = validation.size - wrong.size
        validationTable.row(interpreter.name, correct.toString, validation.size.toString, wrong.mkString(", "))
      }

      println(
        s"Parse: minimum of $trials trials per document after $warmup warm-ups for the JIT " +
          s"(trials repeat parses to at least ${minRunMs.toInt} ms; alloc: heap bytes allocated per parse)"
      )
      val parse = documents.map(loadFixture(suite, _))
      parseTable.header()
      val totals =
        for interpreter <- interpreters yield {
          val measurements = parse.map { document =>
            val m = measure(() => if interpreter.accepts(document.input) then 1 else 0, warmup, trials, minRunMs)
            report(interpreter, document.name, document.bytes.toLong, m.min, m.allocated, m.gcMs, m.accepted == 1)
            m
          }
          val bytes = parse.map(_.bytes.toLong).sum
          val ok    = measurements.forall(_.accepted == 1)
          val gcMs  = measurements.map(_.gcMs).sum
          val total = (measurements.map(_.min).sum, measurements.map(_.allocated).sum)
          report(interpreter, "total", bytes, total._1, total._2, gcMs, ok)
          total
        }
      compare(interpreters, totals)
    }

    private val validationTable = Table(
      Column("interpreter", 16, left = true),
      Column("correct", 7),
      Column("of", 4),
      Column("wrong", 5, left = true),
    )

    private val parseTable = Table(
      Column("interpreter", 16, left = true),
      Column("document", documents.map(_.length).max, left = true),
      Column("size", 8),
      Column("min ms", 9),
      Column("MiB/s", 7),
      Column("alloc MB", 9),
      Column("alloc B/B", 9),
      Column("GC ms", 6),
      Column("accepted", 8),
    )

    private def report(
      interpreter: Interpreter,
      document: String,
      bytes: Long,
      ms: Double,
      allocated: Double,
      gcMs: Long,
      accepted: Boolean,
    ): Unit = {
      parseTable.row(
        interpreter.name,
        document,
        size(bytes),
        decimal(ms, 3),
        decimal(bytes / (1024.0 * 1024.0) / ms * 1000, 1),
        decimal(megabytes(allocated), 2),
        decimal(allocated / bytes, 1),
        gcMs.toString,
        if accepted then "yes" else "NO",
      )
    }
  }

  val suites: List[(String, List[Interpreter] => Unit)] = List(
    "json-test-suite"      -> (runJsonTestSuite(_)),
    "json-dummy-data"      -> (runJsonDummyData(_)),
    "json-benchmark"       -> (TkTech.run(_)),
    "nativejson-benchmark" -> (NativeJson.run(_)),
  )

  /** The flag that adds [[ReferenceParser]] as the baseline, which is slow on the large documents. */
  val referenceFlag = "--reference"

  def main(args: Array[String]): Unit = {
    val (flags, names) = args.toList.partition(_.startsWith("--"))
    val unknown        = names.filterNot(name => suites.exists(_._1 == name)) ++ flags.filterNot(_ == referenceFlag)
    require(
      unknown.isEmpty,
      s"unknown arguments ${unknown.mkString(", ")}; " +
        s"expected $referenceFlag and some of ${suites.map(_._1).mkString(", ")}",
    )
    val interpreters = if flags.contains(referenceFlag) then List(reference, strict) else List(strict)
    JsonFixtures.onDeepStack { () =>
      for (name, run) <- suites if names.isEmpty || names.contains(name) do run(interpreters)
    }
  }
}
