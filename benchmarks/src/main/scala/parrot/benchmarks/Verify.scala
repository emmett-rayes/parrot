package parrot
package benchmarks

import json.{JsonBenchmark, JsonFixtures}

/** Checks the ports of each grammar: on the documents of nativejson-benchmark's Parse Validation and on every document
  * that [[Compare]] measures, every library accepts what the grammar's reference accepts and builds its tree. Prints how
  * the reference does on the Parse Validation, and exits with status 1 if a port disagrees.
  */
object Verify {
  def main(args: Array[String]): Unit = {
    val failures = JsonFixtures.onDeepStack(() => Grammars.all.map(check).sum)
    if failures > 0 then sys.exit(1)
  }

  /** The documents of the Parse Validation, with whether JSON_checker expects them to be accepted. */
  private def validation: List[(String, String, Boolean)] = {
    import JsonBenchmark.NativeJson
    val expected = NativeJson.pass.map(_ -> true) ++ NativeJson.fail.map(_ -> false)
    expected.map((name, valid) => (name, JsonFixtures.load(NativeJson.suite, name).get, valid))
  }

  private def check(grammar: Grammar): Int = {
    val reference = grammar.reference
    println(s"\n=== ${grammar.name}, against ${reference.name} ===")
    val checker = validation.count((_, input, valid) => reference.interpreter.accepts(input) == valid)
    println(s"${reference.name}: $checker of ${validation.size} JSON_checker documents as JSON_checker expects")
    val rejected = Compare.documents.collect { case (name, input) if !reference.interpreter.accepts(input) => name }
    println(s"${reference.name}: rejects ${rejected.size} of the ${Compare.documents.size} measured documents ${rejected.mkString(" ")}")

    val documents = validation.map((name, input, _) => (name, input)) ++ Compare.documents
    var failures  = 0
    for library <- grammar.libraries.tail do {
      val wrong = documents.collect {
        case (name, input) if library.tree(input) != reference.tree(input) => name
      }
      val agreement = if wrong.isEmpty then "agrees" else s"DISAGREES on ${wrong.mkString(" ")}"
      println(s"${library.name}: ${agreement} with ${reference.name} on ${documents.size} documents")
      failures += wrong.size
    }
    failures
  }
}
