package parrot
package parser

import org.scalacheck.{Gen, Prop, Test}
import org.scalatest.funsuite.AnyFunSuite

class ScannerTest extends AnyFunSuite {

  private val supported = List(
    "[ \t\n\r]+",
    "[0-9]+",
    "[1-9][0-9]*",
    "[eE]",
    "[-+]",
    "[0-9A-Fa-f]",
    "[\"/\\\\bfnrt]",
    "[^\"\\\\\\u0000-\\u001f]+",
    "(?s).",
    ".",
    "a?b*c+",
    "\\d+\\.x*",
    "[a-]x?",
    "\\w+\\s*",
    "[^a-d]*d",
    ".+",
    "[^ab]?b",
    "\\S*\\s",
  )

  private val unsupported =
    List("a*a", "[0-9]+[0-9]", "(ab)+", "a|b", "[0-9]{2}", "a+?", "^a", "[a&&b]", "\\p{L}", "\uD83D\uDE00", "\\uD83D")

  /** Single characters, a supplementary character (a surrogate pair), and lone surrogates. */
  private val chars =
    Gen.oneOf("abcdxAzZ09-+.eE \t\n\r\"\\/_\u0001\u00e9\u2028".map(_.toString) ++
      List("\uD83D\uDE00", "\uD83D", "\uDE00"))
  private val inputs = Gen.listOfN(8, chars).map(_.mkString)

  /** Where `regex` matches in `input` from `offset`, as the parsers match it: in context, from the offset. */
  private def matchAt(regex: scala.util.matching.Regex, input: String, offset: Int): Int = {
    val matcher = regex.pattern.matcher(input).nn.region(offset, input.length).nn
    val _       = matcher.useTransparentBounds(true).nn.useAnchoringBounds(false)
    if matcher.lookingAt() then matcher.end() else -1
  }

  test("Scanner agrees with Regex on the supported fragment") {
    for pattern <- supported do {
      val regex   = pattern.r
      val scanner = Scanner.compile(regex)
      val _       = assert(scanner.isDefined, pattern)
      val prop    = Prop.forAll(inputs, Gen.choose(0, 16)) { (input, at) =>
        val offset = at.min(input.length)
        scanner.get.scan(input, offset) == matchAt(regex, input, offset)
      }
      val _ = assert(Test.check(Test.Parameters.default.withMinSuccessfulTests(500), prop).passed, pattern)
    }
  }

  test("Scanner rejects expressions outside the supported fragment") {
    for regex <- unsupported do {
      val _ = assert(Scanner.compile(regex.r).isEmpty, regex)
    }
  }

  test("Scanner reports the first characters and nullability") {
    val digits = Scanner.compile("[0-9]+".r).get.first
    val _      = assert(digits.set.contains('5') && !digits.set.contains('a') && !digits.nullable)
    val sign   = Scanner.compile("-?[0-9]".r).get.first
    val _      = assert(sign.set.contains('-') && sign.set.contains('0') && !sign.nullable)
    val _      = assert(Scanner.compile("a*".r).get.first.nullable)
  }
}
