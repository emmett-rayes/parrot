package parrot
package benchmarks

import json.{JsonBenchmark, JsonFixtures}

/** Measures one library on the valid documents of the data sets of Parrot's JSON benchmark, with each data set's
  * methodology and a warm-up of at least [[warmupMs]] per document:
  * `Compare [--grammar=fastparse] <library> [data set ...]`, Parrot's JsonGrammar and all data sets by default.
  */
object Compare {
  val warmup: Int      = 1
  val warmupMs: Double = 2000
  val minRunMs: Double = 500

  val dataSets: List[(String, JsonBenchmark.Interpreter => Unit)] = List(
    "json-test-suite"      -> validTestSuite,
    "json-dummy-data"      -> (library => JsonBenchmark.runJsonDummyData(List(library), warmup, 7, minRunMs, warmupMs)),
    "json-benchmark"       -> (library => JsonBenchmark.TkTech.run(List(library), warmup, 5, minRunMs, warmupMs)),
    "nativejson-benchmark" -> (library => JsonBenchmark.NativeJson.run(List(library), warmup, minRunMs, warmupMs)),
  )

  /** The valid documents of json-test-suite (y_), grouped as the harness groups them. */
  private def validGroups: List[JsonBenchmark.Group] = {
    JsonBenchmark.groups(JsonFixtures.jsonTestSuite).filter(_.label.startsWith("valid"))
  }

  /** Every document measured, by name. */
  def documents: List[(String, String)] = {
    def load(suite: String, names: List[String]) = names.map(name => (name, JsonFixtures.load(suite, name).get))
    validGroups.flatMap(_.fixtures.map(fixture => (fixture.name, fixture.input)))
      ++ load(JsonFixtures.jsonDummyDataSuite, JsonFixtures.jsonDummyData)
      ++ load(JsonBenchmark.TkTech.suite, JsonBenchmark.TkTech.samples)
      ++ load(JsonBenchmark.NativeJson.suite, JsonBenchmark.NativeJson.documents)
  }

  /** The valid documents (y_) of json-test-suite, as `JsonBenchmark.runJsonTestSuite` measures each group: the median
    * of 7 passes over the documents.
    */
  def validTestSuite(library: JsonBenchmark.Interpreter): Unit = {
    println("\n=== json-test-suite (github.com/nst/JSONTestSuite@1ef36fa, test_parsing), valid documents ===")
    println(
      s"median of 7 runs after a warm-up of at least ${warmupMs.toInt} ms, per pass over the documents " +
        s"(runs repeat passes to at least ${minRunMs.toInt} ms)"
    )
    for group <- validGroups do {
      val pass = () => group.fixtures.count(fixture => library.accepts(fixture.input))
      val m    = JsonBenchmark.measure(pass, warmup, runs = 7, minRunMs, warmupMs)
      val mbs  = group.bytes / 1e6 / m.median * 1000
      println(
        f"${library.name}%-12s ${group.label}%-12s ${group.fixtures.size}%4d documents, ${m.accepted}%4d accepted, " +
          f"${group.bytes}%8d B ${m.median}%9.3f ms $mbs%7.1f MB/s ${m.allocated / 1e6}%8.2f MB alloc"
      )
    }
  }

  def main(args: Array[String]): Unit = {
    val (options, rest) = args.toList.partition(_.startsWith("--"))
    val grammar         = options match {
      case Nil                         => Grammars.parrot
      case List(s"--grammar=$name")    => Grammars.all.find(_.name.equalsIgnoreCase(name)).getOrElse(usage())
      case _                           => usage()
    }
    val library = rest.headOption.flatMap(grammar.library).getOrElse(usage())
    val names   = rest.drop(1)
    println(
      s"${library.name} on ${grammar.name}, Java ${System.getProperty("java.version")} (${System.getProperty("java.vm.name")})"
    )
    JsonFixtures.onDeepStack { () =>
      for (name, run) <- dataSets if names.isEmpty || names.contains(name) do run(library.interpreter)
    }
  }

  private def usage(): Nothing = {
    sys.error(
      s"usage: Compare [--grammar=${Grammars.all.map(_.name).mkString("|")}] " +
        s"<${Grammars.parrot.libraries.map(_.name).mkString("|")}> [${dataSets.map(_._1).mkString("|")} ...]"
    )
  }
}
