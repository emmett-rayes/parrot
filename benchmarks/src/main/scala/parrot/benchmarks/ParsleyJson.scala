package parrot
package benchmarks

import parsley.Parsley
import parsley.Parsley.{atomic, eof, many}
import parsley.character.{char, oneOf, satisfy, string, stringOfSome}
import parsley.combinator.{exactly, option}

/** Parrot's JsonGrammar ported to Parsley: the same nonterminals, building the same tree, with Parsley's Lists where
  * Parrot builds Vectors. Where PEG's ordered choice backtracks over consumed input and Parsley's does not, `atomic`
  * restores it: only the first member of an object and the first element of an array need it, since they begin with
  * optional whitespace that the empty case would otherwise not see.
  */
object ParsleyJson {
  type Number        = (((Option[String], String), Option[String]), Option[(Option[String], String)])
  type UnicodeEscape = List[String]
  type Escape        = String | UnicodeEscape
  type Str           = List[String | Escape]
  type Obj           = List[(Str, Json)] | Option[String]
  type Arr           = List[Json] | Option[String]
  type Value         = Obj | Arr | Str | String | Number

  final case class Json(json: Value)

  private def isDigit(c: Char): Boolean = c >= '0' && c <= '9'
  private def isHex(c: Char): Boolean   = isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

  val s: Parsley[String]          = stringOfSome(c => c == ' ' || c == '\t' || c == '\n' || c == '\r')
  val ws: Parsley[Option[String]] = option(s)

  val jsonTrue: Parsley[String]  = string("true")
  val jsonFalse: Parsley[String] = string("false")
  val jsonNull: Parsley[String]  = string("null")
  val minus: Parsley[String]     = string("-")

  val integralPart: Parsley[String] = {
    string("0") | (satisfy(c => c >= '1' && c <= '9') *> many(satisfy(isDigit)).void).span
  }
  val fractionalPart: Parsley[String]                 = char('.') ~> stringOfSome(isDigit)
  val exponentPart: Parsley[(Option[String], String)] = {
    (oneOf('e', 'E') ~> option(oneOf('-', '+').span)) <~> stringOfSome(isDigit)
  }
  val number: Parsley[Number] = option(minus) <~> integralPart <~> option(fractionalPart) <~> option(exponentPart)

  val unicodeEscape: Parsley[UnicodeEscape] = char('u') ~> exactly(4, satisfy(isHex).span)
  val escape: Parsley[Escape]               = {
    char('\\') ~> ((oneOf('"', '/', '\\', 'b', 'f', 'n', 'r', 't').span: Parsley[Escape]) | unicodeEscape)
  }

  val str: Parsley[Str] = {
    val unescaped                           = stringOfSome(c => c != '"' && c != '\\' && c >= ' ')
    val character: Parsley[String | Escape] = (unescaped: Parsley[String | Escape]) | escape
    ws ~> (char('"') ~> many(character) <~ char('"')) <~ ws
  }

  private def makeObj(value: => Parsley[Json]): Parsley[Obj] = {
    char('{') ~> {
      val member: Parsley[(Str, Json)] = (str <~ char(':')) <~> value
      (atomic(member) <::> many(char(',') ~> member): Parsley[Obj]) | ws
    } <~ char('}')
  }

  private def makeArray(value: => Parsley[Json]): Parsley[Arr] = {
    char('[') ~> {
      (atomic(value) <::> many(char(',') ~> value): Parsley[Arr]) | ws
    } <~ char(']')
  }

  lazy val json: Parsley[Json] = {
    val value: Parsley[Value] =
      (makeObj(json): Parsley[Value]) | makeArray(json) | str | (jsonTrue | jsonFalse | jsonNull) | number
    (ws ~> value <~ ws).map(Json(_))
  }

  /** A whole document. */
  val document: Parsley[Json] = json <~ eof

  def parseDocument(input: String): Option[Json] = document.parse(input).toOption
}
