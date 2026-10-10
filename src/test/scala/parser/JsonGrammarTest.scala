package parrot
package parser

import org.scalatest.funsuite.AnyFunSuite

/** The JSON grammar tests, ported from the legacy interpreter and run on every interpreter. */
class JsonGrammarTest extends AnyFunSuite {

  given CanEqual[Any, Any] = CanEqual.derived

  private val reference = JsonGrammar(ReferenceParser)
  private val strict    = JsonGrammar(StrictParser)

  tests("ReferenceParser", reference)([B] =>
    (p: reference.algebra.P[Unit, B], input: String) =>
      ReferenceParser.parse(p)(input) match {
        case ReferenceParser.Result.Success(value, offset) => Some((value, input.substring(offset)))
        case ReferenceParser.Result.Failure(_, _)          => None
      }
  )

  tests("StrictParser", strict)([B] =>
    (p: strict.algebra.P[Unit, B], input: String) =>
      StrictParser.parse(p)(input).toOption.map(r => (r.value, input.substring(r.offset)))
  )

  /** Registers the tests of `grammar`, given a way to `run` a parser on a prefix of the input, returning its result and
    * the remaining input.
    */
  private def tests(interpreter: String, grammar: JsonGrammar)(
    run: [B] => (grammar.algebra.P[Unit, B], String) => Option[(B, String)]
  ): Unit = {
    extension [B](self: grammar.algebra.P[Unit, B]) def on(input: String): Option[(B, String)] = run(self, input)

    def accepts[B](p: grammar.algebra.P[Unit, B], input: String): Boolean = p.on(input).exists(_._2.isEmpty)

    test(s"$interpreter: s consumes whitespace") {
      val _ = assert(grammar.s.on("   rest") == Some(("   ", "rest")))
      val _ = assert(grammar.s.on("\t\n\rrest") == Some(("\t\n\r", "rest")))
      val _ = assert(grammar.s.on("no_ws").isEmpty)
    }

    test(s"$interpreter: jsonTrue, jsonFalse and jsonNull parse their keywords") {
      val _ = assert(grammar.jsonTrue.on("true_extra") == Some(("true", "_extra")))
      val _ = assert(grammar.jsonTrue.on("false").isEmpty)
      val _ = assert(grammar.jsonFalse.on("false") == Some(("false", "")))
      val _ = assert(grammar.jsonFalse.on("true").isEmpty)
      val _ = assert(grammar.jsonNull.on("null_extra") == Some(("null", "_extra")))
      val _ = assert(grammar.jsonNull.on("nil").isEmpty)
    }

    test(s"$interpreter: number parses various numbers") {
      for input <- List("0", "-42", "123.456", "-123.456e+78", "0E-2") do {
        val _ = assert(accepts(grammar.number, input), input)
      }
      val _ = assert(grammar.number.on("-123.456e+78").map(_._1) ==
        Some((((Some("-"), "123"), Some("456")), Some((Some("+"), "78")))))
      val _ = assert(grammar.number.on("01") == Some(((((None, "0"), None), None), "1")))
    }

    test(s"$interpreter: unicodeEscape parses 4 hex digits") {
      val _ = assert(grammar.unicodeEscape.on("u0020rest") == Some((Vector("0", "0", "2", "0"), "rest")))
      val _ = assert(grammar.unicodeEscape.on("u12AFrest") == Some((Vector("1", "2", "A", "F"), "rest")))
      val _ = assert(grammar.unicodeEscape.on("u12").isEmpty)
    }

    test(s"$interpreter: escape parses escape sequences") {
      val _ = assert(grammar.escape.on("\\\"rest") == Some(("\"", "rest")))
      val _ = assert(grammar.escape.on("\\\\rest") == Some(("\\", "rest")))
      val _ = assert(grammar.escape.on("\\nrest") == Some(("n", "rest")))
      val _ = assert(grammar.escape.on("\\u0041rest") == Some((Vector("0", "0", "4", "1"), "rest")))
    }

    test(s"$interpreter: string parses quoted strings with escapes and whitespace") {
      val _ = assert(grammar.string.on("\"hello\"") == Some((Vector("hello"), "")))
      val _ = assert(grammar.string.on("\"\"") == Some((Vector.empty, "")))
      val _ = assert(grammar.string.on("  \"with whitespace\"  ") == Some((Vector("with whitespace"), "")))
      val _ =
        assert(grammar.string.on("\"escape: \\n and \\\"\"") == Some((Vector("escape: ", "n", " and ", "\""), "")))
    }

    test(s"$interpreter: array parses empty and non-empty arrays") {
      val _ = assert(grammar.array.on("[]") == Some((None, "")))
      val _ = assert(grammar.array.on("[  ]") == Some((Some("  "), "")))
      val _ = assert(accepts(grammar.array, "[1, 2, 3]"))
    }

    test(s"$interpreter: obj parses empty and non-empty objects") {
      val _ = assert(grammar.obj.on("{}") == Some((None, "")))
      val _ = assert(grammar.obj.on("{  }") == Some((Some("  "), "")))
      val _ = assert(accepts(grammar.obj, "{\"key\": \"val\"}"))
    }

    test(s"$interpreter: json parses valid JSON documents") {
      val samples = List(
        "true",
        "false",
        "null",
        "42",
        "-3.14159",
        "\"hello world\"",
        "[]",
        "[1, true, \"three\", null]",
        "{}",
        "{\"name\": \"Alice\", \"age\": 30}",
        """
          {
            "glossary": {
              "title": "example glossary",
              "GlossDiv": {
                "title": "S",
                "GlossList": {
                  "GlossEntry": {
                    "ID": "SGML",
                    "SortAs": "SGML",
                    "GlossTerm": "Standard Generalized Markup Language",
                    "Acronym": "SGML",
                    "Abbrev": "ISO 8879:1986",
                    "GlossDef": {
                      "para": "A meta-markup language.",
                      "GlossSeeAlso": ["GML", "XML"]
                    },
                    "GlossSee": "markup"
                  }
                }
              }
            }
          }
        """,
      )
      for sample <- samples do {
        val _ = assert(accepts(grammar.json, sample), sample)
      }
    }

    test(s"$interpreter: json rejects invalid JSON") {
      val samples = List("{", "}", "[", "]", "{\"foo\": }", "{\"foo\" \"bar\"}", "[1, 2, ]", "undefined")
      for sample <- samples do {
        val _ = assert(!accepts(grammar.json, sample), sample)
      }
    }
  }
}
