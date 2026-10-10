package parrot
package parser

import java.lang.management.ManagementFactory
import java.net.URI
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, StandardCopyOption}
import scala.jdk.CollectionConverters.*

/** Compares the throughput and memory usage of the interpreters on the JSON grammar, with three suites run one after
  * the other and reported separately:
  *   - `JSONTestSuite`: the `test_parsing` documents of [[https://github.com/nst/JSONTestSuite]] (vendored in
  *     [[JsonFixtures]]), grouped by expectation
  *   - `json-dummy-data`: the documents of [[https://microsoftedge.github.io/Demos/json-dummy-data]] (vendored in
  *     [[JsonFixtures]]), one by one
  *   - `json_benchmark`: the sample documents of [[https://github.com/TkTech/json_benchmark]], with its methodology
  *   - `nativejson-benchmark`: the Parse and Parse Validation benchmarks of
  *     [[https://github.com/miloyip/nativejson-benchmark]], with its methodology
  *
  * Run with `sbt "Test/runMain parrot.parser.JsonBenchmark [--reference] [suite ...]"`; without suites, all suites run.
  * Only [[StrictParser]] is measured unless `--reference` adds [[ReferenceParser]] as the baseline it is compared with;
  * the reference is slow, especially on the large documents of `json_benchmark`. Each external suite first downloads
  * all of its documents that are not cached yet, from a pinned commit into `target/benchmark-data`.
  *
  * Memory is the number of bytes allocated on the heap by the parsing thread, also per byte of input, and the time
  * spent in garbage collection during the measured runs. Garbage is collected before each measured run, so that runs do
  * not pay for the garbage of earlier ones, and the heap has a fixed size (see `build.sbt`).
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

  /** A decoded document and its size in bytes. */
  final case class Fixture(name: String, input: String, bytes: Int)

  private def decode(bytes: Array[Byte]): String = {
    StandardCharsets.UTF_8.newDecoder().decode(java.nio.ByteBuffer.wrap(bytes)).toString
  }

  // ===========================================================================
  // Measurement
  // ===========================================================================

  /** The bytes allocated so far by the current thread. */
  private def allocatedBytes(): Long = {
    ManagementFactory.getThreadMXBean match {
      case threads: com.sun.management.ThreadMXBean => threads.getCurrentThreadAllocatedBytes
      case _                                         => throw UnsupportedOperationException("allocation counters")
    }
  }

  /** The time spent in garbage collection so far, in milliseconds. */
  private def gcMillis(): Long = {
    ManagementFactory.getGarbageCollectorMXBeans.asScala.map(_.getCollectionTime.max(0)).sum
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
    val memory = ManagementFactory.getMemoryMXBean
    var used   = Long.MaxValue
    var rounds = 0
    while rounds < 5 && memory.getHeapMemoryUsage.getUsed < used do {
      used = memory.getHeapMemoryUsage.getUsed
      System.gc()
      rounds += 1
    }
  }

  /** Measures `runs` runs of `work` after `warmup` runs. Each run repeats `work` until it takes at least `minRunMs`, so
    * that small documents are timed reliably, and samples are reported per repetition.
    *
    * Garbage is collected before each run, outside of the measurement, so that the garbage collection time of a run
    * (counted in [[Measurement.gcMs]]) is only due to its own allocations.
    */
  def measure(work: () => Int, warmup: Int, runs: Int, minRunMs: Double = 0): Measurement = {
    var accepted = 0
    var slowest  = 0.0
    for _ <- 1 to warmup.max(1) do {
      val start = System.nanoTime()
      accepted = work()
      slowest = slowest.max((System.nanoTime() - start) / 1e6)
    }
    val repetitions = if slowest >= minRunMs then 1 else math.ceil(minRunMs / slowest.max(1e-3)).toInt
    var gcMs        = 0L
    val samples     = (1 to runs).map { _ =>
      collectGarbage()
      val gcBefore = gcMillis()
      val bytes    = allocatedBytes()
      val start    = System.nanoTime()
      for _ <- 1 to repetitions do accepted = work()
      val ms = (System.nanoTime() - start) / 1e6
      gcMs += gcMillis() - gcBefore
      Sample(ms / repetitions, (allocatedBytes() - bytes).toDouble / repetitions)
    }
    Measurement(samples, gcMs, accepted)
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

  // ===========================================================================
  // External corpora
  // ===========================================================================

  /** The documents at `paths` in a GitHub `repository` at `commit`, cached in `target/benchmark-data`. */
  final case class Corpus(repository: String, commit: String, paths: List[String]) {
    private val cache = Path.of("target", "benchmark-data", repository.replace('/', '_'), commit)

    def source: String = s"github.com/$repository@${commit.take(7)}"

    /** Downloads the documents that are not cached yet, all before any of them is used. */
    def download(): Unit = {
      val missing = paths.filterNot(path => Files.exists(cache.resolve(path)))
      if missing.nonEmpty then {
        print(s"downloading ${missing.size} of ${paths.size} documents from $source ...")
        for path <- missing do {
          val file = cache.resolve(path)
          val _    = Files.createDirectories(file.getParent)
          val part = Files.createTempFile(file.getParent, file.getFileName.toString, ".part")
          val in   = URI.create(s"https://raw.githubusercontent.com/$repository/$commit/$path").toURL.openStream()
          try {
            val _ = Files.copy(in, part, StandardCopyOption.REPLACE_EXISTING)
          } finally in.close()
          val _ = Files.move(part, file, StandardCopyOption.ATOMIC_MOVE)
        }
        println(" done")
      }
    }

    /** The [[download]]ed document at `path`. */
    def load(path: String): Fixture = {
      require(paths.contains(path), s"$path is not in the corpus of $source")
      val file  = cache.resolve(path)
      val bytes = Files.readAllBytes(file)
      Fixture(file.getFileName.toString, decode(bytes), bytes.length)
    }
  }

  // ===========================================================================
  // JSONTestSuite
  // ===========================================================================

  /** A group of fixtures, measured together. */
  final case class Group(label: String, fixtures: List[Fixture]) {
    val bytes: Long = fixtures.map(_.bytes.toLong).sum
  }

  /** The [[JsonFixtures]] that are valid UTF-8, grouped by expectation. */
  def groups(names: List[String]): List[Group] = {
    val fixtures = names.flatMap { name =>
      JsonFixtures.load(name).toOption.map(Fixture(name, _, JsonFixtures.bytes(name).length))
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
    heading("JSONTestSuite (github.com/nst/JSONTestSuite@1ef36fa, test_parsing)")
    println(
      s"${suite.map(_.fixtures.size).sum} fixtures, ${size(bytes)}: " +
        s"median of $runs runs after $warmup warm-ups, per pass over the fixtures " +
        s"(runs repeat passes to at least ${minRunMs.toInt} ms; alloc: heap bytes allocated per pass)"
    )
    groupTable.header()
    val totals = for interpreter <- interpreters yield {
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

  // ===========================================================================
  // json_benchmark
  // ===========================================================================

  /** [[https://github.com/TkTech/json_benchmark]]: complete loads of each sample document, reported per document by the
    * minimum, maximum and mean duration, as by `pytest-benchmark`.
    */
  object TkTech {
    /** The `SAMPLE_FILES` of `tests/conftest.py`, in order. */
    val samples: List[String] = List(
      "data/canada.json",
      "data/citm_catalog.json",
      "data/twitter.json",
      "data/verysmall.json",
      "data/fgo.json",
      "data/otfcc.json",
      "data/poet.json",
      "data/gsoc-2018.json",
    )

    val corpus: Corpus = Corpus("TkTech/json_benchmark", "52d596b8a9bc0e00e654747298a8ec5b0d95152b", samples)

    def run(interpreters: List[Interpreter], warmup: Int = 1, runs: Int = 5, minRunMs: Double = 100): Unit = {
      heading(s"json_benchmark (${corpus.source})")
      corpus.download()
      println(
        s"complete load of each document: min, max and mean of $runs runs after $warmup warm-up, per load " +
          s"(runs repeat loads to at least ${minRunMs.toInt} ms; alloc: heap bytes allocated per load)"
      )
      val table = documentTable(samples)
      table.header()
      for path <- samples do {
        loadEach(table, interpreters, path, corpus.load(path), warmup, runs, minRunMs)
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

  // ===========================================================================
  // json-dummy-data
  // ===========================================================================

  /** The documents of [[https://microsoftedge.github.io/Demos/json-dummy-data]], vendored in [[JsonFixtures]], loaded
    * one by one and reported like `json_benchmark`.
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
    val table = documentTable(JsonFixtures.jsonDummyData)
    table.header()
    for name <- JsonFixtures.jsonDummyData do {
      val document = Fixture(name, JsonFixtures.load(name).get, JsonFixtures.bytes(name).length)
      loadEach(table, interpreters, name, document, warmup, runs, minRunMs)
    }
  }

  // ===========================================================================
  // nativejson-benchmark
  // ===========================================================================

  /** [[https://github.com/miloyip/nativejson-benchmark]]:
    *   - Parse Validation: the JSON_checker documents `pass*.json` must be accepted and `fail*.json` rejected, except
    *     `fail01.json` (relaxed by RFC 7159) and `fail18.json` (nesting depth is unspecified)
    *   - Parse: each document is parsed in 10 trials, reported by the minimum duration and the throughput in MiB/s,
    *     per document and as the total over the documents
    */
  object NativeJson {
    /** `data/data.txt`. */
    val documents: List[String] = List("data/canada.json", "data/citm_catalog.json", "data/twitter.json")

    val pass: List[String] = (1 to 3).map(i => f"data/jsonchecker/pass$i%02d.json").toList

    val fail: List[String] = (2 to 33).filterNot(_ == 18).map(i => f"data/jsonchecker/fail$i%02d.json").toList

    val corpus: Corpus = {
      Corpus("miloyip/nativejson-benchmark", "478d5727c2a4048e835a29c65adecc7d795360d5", documents ++ pass ++ fail)
    }

    val trials = 10

    def run(interpreters: List[Interpreter], warmup: Int = 3, minRunMs: Double = 100): Unit = {
      heading(s"nativejson-benchmark (${corpus.source})")
      corpus.download()

      println("Parse Validation (JSON_checker): pass*.json accepted, fail*.json rejected")
      val validation = pass.map(corpus.load(_) -> true) ++ fail.map(corpus.load(_) -> false)
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
      val parse  = documents.map(corpus.load)
      parseTable.header()
      val totals = for interpreter <- interpreters yield {
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
      Column("document", documents.map(_.stripPrefix("data/").length).max, left = true),
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

  // ===========================================================================
  // Entry point
  // ===========================================================================

  val suites: List[(String, List[Interpreter] => Unit)] = List(
    "JSONTestSuite"        -> (runJsonTestSuite(_)),
    "json-dummy-data"      -> (runJsonDummyData(_)),
    "json_benchmark"       -> (TkTech.run(_)),
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
    for (name, run) <- suites if names.isEmpty || names.contains(name) do run(interpreters)
  }
}
