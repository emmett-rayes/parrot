package parrot
package benchmarks

import org.parboiled2.*

/** Parrot's JsonGrammar ported to parboiled2: the same nonterminals, building the same tree, with the nested tuples of
  * Parrot's sequences built by actions. Its `|` is PEG's ordered choice.
  */
object Parboiled2Json {
  type Number        = (((Option[String], String), Option[String]), Option[(Option[String], String)])
  type UnicodeEscape = Seq[String]
  type Escape        = String | UnicodeEscape
  type Str           = Seq[String | Escape]
  type Obj           = Seq[(Str, Json)] | Option[String]
  type Arr           = Seq[Json] | Option[String]
  type Value         = Obj | Arr | Str | String | Number

  final case class Json(json: Value)

  val Space: CharPredicate     = CharPredicate(" \t\n\r")
  val Unescaped: CharPredicate = CharPredicate.from(c => c != '"' && c != '\\' && c >= ' ')
  val Digit19: CharPredicate   = CharPredicate('1' to '9')

  def parseDocument(input: String): Option[Json] = Parboiled2Json(input).document.run().toOption
}

final class Parboiled2Json(val input: ParserInput) extends Parser {
  import Parboiled2Json.*
  import CharPredicate.{Digit, HexDigit}

  def s: Rule1[String]          = rule(capture(oneOrMore(Space)))
  def ws: Rule1[Option[String]] = rule(optional(s))

  def jsonTrue: Rule1[String]  = rule(capture("true"))
  def jsonFalse: Rule1[String] = rule(capture("false"))
  def jsonNull: Rule1[String]  = rule(capture("null"))
  def minus: Rule1[String]     = rule(capture("-"))

  def integralPart: Rule1[String]   = rule(capture("0") | capture(Digit19 ~ zeroOrMore(Digit)))
  def fractionalPart: Rule1[String] = rule('.' ~ capture(oneOrMore(Digit)))

  def exponentPart: Rule1[(Option[String], String)] = rule {
    anyOf("eE") ~ optional(capture(anyOf("+-"))) ~ capture(oneOrMore(Digit)) ~>
      ((sign: Option[String], digits: String) => (sign, digits))
  }

  def number: Rule1[Number] = rule {
    optional(minus) ~ integralPart ~ optional(fractionalPart) ~ optional(exponentPart) ~>
      ((m: Option[String], i: String, f: Option[String], e: Option[(Option[String], String)]) => (((m, i), f), e))
  }

  def unicodeEscape: Rule1[UnicodeEscape] = rule('u' ~ 4.times(capture(HexDigit)))

  def escape: Rule1[Escape] = rule {
    '\\' ~ (capture(anyOf("\"/\\bfnrt")) ~> ((c: String) => c: Escape) | unicodeEscape ~> ((u: UnicodeEscape) => u: Escape))
  }

  def character: Rule1[String | Escape] = rule {
    capture(oneOrMore(Unescaped)) ~> ((u: String) => u: String | Escape) | escape ~> ((e: Escape) => e: String | Escape)
  }

  def jsonString: Rule1[Str] = rule {
    ws ~ '"' ~ zeroOrMore(character) ~ '"' ~ ws ~> ((_: Option[String], cs: Seq[String | Escape], _: Option[String]) => cs)
  }

  def member: Rule1[(Str, Json)] = rule(jsonString ~ ':' ~ json ~> ((k: Str, v: Json) => (k, v)))

  def obj: Rule1[Obj] = rule {
    '{' ~ (oneOrMore(member).separatedBy(',') ~> ((ms: Seq[(Str, Json)]) => ms: Obj) | ws ~> ((w: Option[String]) => w: Obj)) ~ '}'
  }

  def array: Rule1[Arr] = rule {
    '[' ~ (oneOrMore(json).separatedBy(',') ~> ((xs: Seq[Json]) => xs: Arr) | ws ~> ((w: Option[String]) => w: Arr)) ~ ']'
  }

  def value: Rule1[Value] = rule {
    obj ~> ((o: Obj) => o: Value)
      | array ~> ((a: Arr) => a: Value)
      | jsonString ~> ((t: Str) => t: Value)
      | (jsonTrue | jsonFalse | jsonNull) ~> ((l: String) => l: Value)
      | number ~> ((n: Number) => n: Value)
  }

  def json: Rule1[Json] = rule(ws ~ value ~ ws ~> ((_: Option[String], v: Value, _: Option[String]) => Json(v)))

  /** A whole document. */
  def document: Rule1[Json] = rule(json ~ EOI)
}
