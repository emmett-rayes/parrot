package parrot
package benchmarks

import org.parboiled2.*

/** fastparse's documented JSON grammar ([[FastparseJs]]) ported to parboiled2, into [[Js]]: `capture` for fastparse's
  * `.!`. parboiled2 has no cuts; its `|` backtracks, which accepts the same documents here.
  */
object Parboiled2Js {
  val Space: CharPredicate       = CharPredicate(" \r\n")
  val Digit19: CharPredicate     = CharPredicate('1' to '9')
  val StringChars: CharPredicate = CharPredicate.from(c => c != '"' && c != '\\')

  def parseDocument(input: String): Option[Js.Val] = Parboiled2Js(input).document.run().toOption
}

final class Parboiled2Js(val input: ParserInput) extends Parser {
  import Parboiled2Js.*
  import CharPredicate.{Digit, HexDigit}

  def space: Rule0      = rule(zeroOrMore(Space))
  def digits: Rule0     = rule(oneOrMore(Digit))
  def exponent: Rule0   = rule(anyOf("eE") ~ optional(anyOf("+-")) ~ digits)
  def fractional: Rule0 = rule('.' ~ digits)
  def integral: Rule0   = rule('0' | Digit19 ~ optional(digits))

  def number: Rule1[Js.Val] = rule {
    capture(optional(anyOf("+-")) ~ integral ~ optional(fractional) ~ optional(exponent)) ~>
      ((x: String) => Js.Num(x.toDouble))
  }

  def jsonNull: Rule1[Js.Val]  = rule("null" ~ push(Js.Null))
  def jsonFalse: Rule1[Js.Val] = rule("false" ~ push(Js.False))
  def jsonTrue: Rule1[Js.Val]  = rule("true" ~ push(Js.True))

  def hexDigit: Rule0      = rule(HexDigit)
  def unicodeEscape: Rule0 = rule('u' ~ hexDigit ~ hexDigit ~ hexDigit ~ hexDigit)
  def escape: Rule0        = rule('\\' ~ (anyOf("\"/\\bfnrt") | unicodeEscape))

  def strChars: Rule0 = rule(oneOrMore(StringChars))

  /** The text of a string, without its quotes. */
  def jsonString: Rule1[String] = rule(space ~ '"' ~ capture(zeroOrMore(strChars | escape)) ~ '"')

  def array: Rule1[Js.Val] = rule {
    '[' ~ zeroOrMore(jsonExpr).separatedBy(',') ~ space ~ ']' ~> ((values: Seq[Js.Val]) => Js.Arr(values))
  }

  def pair: Rule1[(String, Js.Val)] = rule(jsonString ~ ':' ~ jsonExpr ~> ((k: String, v: Js.Val) => (k, v)))

  def obj: Rule1[Js.Val] = rule {
    '{' ~ zeroOrMore(pair).separatedBy(',') ~ space ~ '}' ~> ((pairs: Seq[(String, Js.Val)]) => Js.Obj(pairs))
  }

  def stringValue: Rule1[Js.Val] = rule(jsonString ~> ((s: String) => Js.Str(s)))

  def jsonExpr: Rule1[Js.Val] = rule {
    space ~ (obj | array | stringValue | jsonTrue | jsonFalse | jsonNull | number) ~ space
  }

  /** A whole document. */
  def document: Rule1[Js.Val] = rule(jsonExpr ~ EOI)
}
