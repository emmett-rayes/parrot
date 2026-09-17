package parrot

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Success

class JsonGrammarTest extends AnyFunSuite {
  import Parser.{run, given}

  private val grammar = JsonGrammar[Parser]
  private val P       = ParserAlgebra[Parser]

  test("s parses whitespace") {
    assert(
      grammar.s.run("   abc") == Success(("   ", "abc")) &&
        grammar.s.run("\t\n\r foo") == Success(("\t\n\r ", "foo")) &&
        grammar.s.run("abc").isFailure,
    )
  }

  test("times executes parser exactly n times") {
    val parser = P.literal("a").times(3)
    assert(
      parser.run("aaarest") == Success((result = List("a", "a", "a"), state = "rest")) &&
        parser.run("aaa") == Success((result = List("a", "a", "a"), state = "")) &&
        parser.run("aa").isFailure &&
        parser.run("").isFailure &&
        P.literal("a").times(0).run("rest") == Success((result = List.empty, state = "rest")) &&
        P.literal("a").times(0).run("") == Success((result = List.empty, state = "")),
    )
  }

  test("jsonTrue parses true") {
    assert(
      grammar.jsonTrue.run("true, rest") == Success(("true", ", rest")) &&
        grammar.jsonTrue.run("false").isFailure,
    )
  }

  test("jsonFalse parses false") {
    assert(
      grammar.jsonFalse.run("false, rest") == Success(("false", ", rest")) &&
        grammar.jsonFalse.run("true").isFailure,
    )
  }

  test("jsonNull parses null") {
    assert(
      grammar.jsonNull.run("null, rest") == Success(("null", ", rest")) &&
        grammar.jsonNull.run("nil").isFailure,
    )
  }

  test("number parses various numbers") {
    val res0     = grammar.number.run("0")
    val resNeg   = grammar.number.run("-42")
    val resFloat = grammar.number.run("123.456")
    val resSci   = grammar.number.run("-123.456e+78")
    val resSci2  = grammar.number.run("0E-2")
    assert(
      res0.isSuccess && res0.get.state.isEmpty &&
        resNeg.isSuccess && resNeg.get.state.isEmpty &&
        resFloat.isSuccess && resFloat.get.state.isEmpty &&
        resSci.isSuccess && resSci.get.state.isEmpty &&
        resSci2.isSuccess && resSci2.get.state.isEmpty,
    )
  }

  test("unicodeEscape parses 4 hex digits") {
    assert(
      grammar.unicodeEscape.run("u0020rest") == Success((List("0", "0", "2", "0"), "rest")) &&
        grammar.unicodeEscape.run("u12AFrest") == Success((List("1", "2", "A", "F"), "rest")) &&
        grammar.unicodeEscape.run("u12").isFailure,
    )
  }

  test("escape parses escape sequences") {
    assert(
      grammar.escape.run("\\\"rest") == Success(("\"", "rest")) &&
        grammar.escape.run("\\\\rest") == Success(("\\", "rest")) &&
        grammar.escape.run("\\nrest") == Success(("n", "rest")) &&
        grammar.escape.run("\\u0041rest") == Success((List("0", "0", "4", "1"), "rest")),
    )
  }

  test("string parses quoted strings with escapes and whitespace") {
    assert(
      grammar.string.run("\"hello\"") == Success((List("h", "e", "l", "l", "o"), "")) &&
        grammar.string.run("\"\"") == Success((List.empty, "")) &&
        grammar.string.run("  \"with whitespace\"  ") == Success((
          List("w", "i", "t", "h", " ", "w", "h", "i", "t", "e", "s", "p", "a", "c", "e"),
          "",
        )) &&
        grammar.string.run("\"escape: \\n and \\\"\"") == Success((
          List("e", "s", "c", "a", "p", "e", ":", " ", "n", " ", "a", "n", "d", " ", "\""),
          "",
        )),
    )
  }

  test("array parses empty and non-empty arrays") {
    val res = grammar.array.run("[1, 2, 3]")
    assert(
      grammar.array.run("[]") == Success((None, "")) &&
        grammar.array.run("[  ]") == Success((Some("  "), "")) &&
        res.isSuccess && res.get.state.isEmpty,
    )
  }

  test("obj parses empty and non-empty objects") {
    val res = grammar.obj.run("{\"key\": \"val\"}")
    assert(
      grammar.obj.run("{}") == Success((None, "")) &&
        grammar.obj.run("{  }") == Success((Some("  "), "")) &&
        res.isSuccess && res.get.state.isEmpty,
    )
  }

  test("json parses valid JSON documents") {
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

    val allParsed = samples.forall { sample =>
      val res = grammar.json.run(sample)
      res.isSuccess && res.get.state.isEmpty
    }
    assert(allParsed)
  }

  test("json rejects invalid JSON") {
    val invalidSamples = List(
      "{",
      "}",
      "[",
      "]",
      "{\"foo\": }",
      "{\"foo\" \"bar\"}",
      "[1, 2, ]",
      "undefined",
    )

    val allRejected = invalidSamples.forall { sample =>
      val res = grammar.json.run(sample)
      !(res.isSuccess && res.get.state.isEmpty)
    }
    assert(allRejected)
  }
}
