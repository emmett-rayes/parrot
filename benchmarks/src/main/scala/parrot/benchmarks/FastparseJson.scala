package parrot
package benchmarks

import fastparse.*
import fastparse.NoWhitespace.*

/** Parrot's JsonGrammar ported to fastparse: the same nonterminals, building the same tree, with fastparse's Seqs where
  * Parrot builds Vectors and its flat tuple for a number. Its `|` backtracks like PEG's ordered choice.
  */
object FastparseJson {
  type Number        = (Option[String], String, Option[String], Option[(Option[String], String)])
  type UnicodeEscape = Seq[String]
  type Escape        = String | UnicodeEscape
  type Str           = Seq[String | Escape]
  type Obj           = Seq[(Str, Json)] | Option[String]
  type Arr           = Seq[Json] | Option[String]
  type Value         = Obj | Arr | Str | String | Number

  final case class Json(json: Value)

  def s[$: P]: P[String]          = P(CharsWhileIn(" \t\n\r").!)
  def ws[$: P]: P[Option[String]] = P(s.?)

  def jsonTrue[$: P]: P[String]  = P("true".!)
  def jsonFalse[$: P]: P[String] = P("false".!)
  def jsonNull[$: P]: P[String]  = P("null".!)
  def minus[$: P]: P[String]     = P("-".!)

  def integralPart[$: P]: P[String]                   = P("0".! | (CharIn("1-9") ~ CharsWhileIn("0-9", 0)).!)
  def fractionalPart[$: P]: P[String]                 = P("." ~ CharsWhileIn("0-9").!)
  def exponentPart[$: P]: P[(Option[String], String)] = P(CharIn("eE") ~ CharIn("+\\-").!.? ~ CharsWhileIn("0-9").!)
  def number[$: P]: P[Number]                         = P(minus.? ~ integralPart ~ fractionalPart.? ~ exponentPart.?)

  def unicodeEscape[$: P]: P[UnicodeEscape] = P("u" ~ CharIn("0-9a-fA-F").!.rep(exactly = 4))
  def escape[$: P]: P[Escape]               = P("\\" ~ ((CharIn("\"/\\\\bfnrt").! : P[Escape]) | unicodeEscape))

  def unescaped[$: P]: P[String]          = P(CharsWhile(c => c != '"' && c != '\\' && c >= ' ').!)
  def character[$: P]: P[String | Escape] = P((unescaped: P[String | Escape]) | escape)
  def str[$: P]: P[Str]                   = P(ws ~ "\"" ~ character.rep ~ "\"" ~ ws).map(_._2)

  def member[$: P]: P[(Str, Json)] = P(str ~ ":" ~ json)
  def obj[$: P]: P[Obj]            = P("{" ~ ((member.rep(min = 1, sep = ","): P[Obj]) | ws) ~ "}")
  def array[$: P]: P[Arr]          = P("[" ~ ((json.rep(min = 1, sep = ","): P[Arr]) | ws) ~ "]")

  def json[$: P]: P[Json] = {
    P(ws ~ ((obj: P[Value]) | array | str | (jsonTrue | jsonFalse | jsonNull) | number) ~ ws).map(t => Json(t._2))
  }

  /** A whole document. */
  def document[$: P]: P[Json] = P(json ~ End)

  def parseDocument(input: String): Option[Json] = {
    fastparse.parse(input, document(using _)) match {
      case Parsed.Success(json, _) => Some(json)
      case _: Parsed.Failure       => None
    }
  }
}
