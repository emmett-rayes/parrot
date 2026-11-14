package parrot
package benchmarks

import cats.parse.{Parser as P, Parser0 as P0}

/** Parrot's JsonGrammar ported to cats-parse: the same nonterminals, building the same tree, with Lists where Parrot
  * builds Vectors. Its `|` does not backtrack over consumed input, so the bodies of objects and arrays, which begin with
  * optional whitespace, `backtrack` to their empty case.
  */
object CatsParseJson {
  type Number        = (((Option[String], String), Option[String]), Option[(Option[String], String)])
  type UnicodeEscape = List[String]
  type Escape        = String | UnicodeEscape
  type Str           = List[String | Escape]
  type Obj           = List[(Str, Json)] | Option[String]
  type Arr           = List[Json] | Option[String]
  type Value         = Obj | Arr | Str | String | Number

  final case class Json(json: Value)

  private def isDigit(c: Char): Boolean = c >= '0' && c <= '9'

  val s: P[String]           = P.charsWhile(c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
  val ws: P0[Option[String]] = s.?

  val jsonTrue: P[String]  = P.string("true").string
  val jsonFalse: P[String] = P.string("false").string
  val jsonNull: P[String]  = P.string("null").string
  val minus: P[String]     = P.char('-').string

  val integralPart: P[String]                   = P.char('0').string | (P.charIn('1' to '9') ~ P.charsWhile0(isDigit)).string
  val fractionalPart: P[String]                 = P.char('.') *> P.charsWhile(isDigit)
  val exponentPart: P[(Option[String], String)] = (P.charIn('e', 'E') *> P.charIn('-', '+').string.?) ~ P.charsWhile(isDigit)
  val number: P[Number]                         = minus.?.with1 ~ integralPart ~ fractionalPart.? ~ exponentPart.?

  private val hex                           = P.charIn(('0' to '9') ++ ('a' to 'f') ++ ('A' to 'F')).string
  val unicodeEscape: P[UnicodeEscape]       = P.char('u') *> hex.repExactlyAs[List[String]](4)
  val escape: P[Escape]                     = P.char('\\') *> ((P.charIn("\"/\\bfnrt".toList).string: P[Escape]) | unicodeEscape)
  val unescaped: P[String]                  = P.charsWhile(c => c != '"' && c != '\\' && c >= ' ')
  val character: P[String | Escape]         = (unescaped: P[String | Escape]) | escape
  val str: P[Str]                           = (ws.with1 *> (P.char('"') *> character.rep0 <* P.char('"'))) <* ws

  val json: P[Json] = P.recursive[Json] { json =>
    val member: P[(Str, Json)] = (str <* P.char(':')) ~ json
    val obj: P[Obj] = P.char('{') *> ((member.repSep(P.char(',')).backtrack.map(_.toList): P0[Obj]) | ws) <* P.char('}')
    val arr: P[Arr] = P.char('[') *> ((json.repSep(P.char(',')).backtrack.map(_.toList): P0[Arr]) | ws) <* P.char(']')
    val value: P[Value] = (obj: P[Value]) | arr | str | (jsonTrue | jsonFalse | jsonNull) | number
    (ws.with1 *> value <* ws).map(Json(_))
  }

  def parseDocument(input: String): Option[Json] = json.parseAll(input).toOption
}
