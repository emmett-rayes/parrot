package parrot
package benchmarks

import fastparse.*
import fastparse.NoWhitespace.*

/** fastparse's JSON grammar as its documentation writes it (com-lihaoyi.github.io/fastparse, section Json), into [[Js]],
  * with `End` after the value for whole documents.
  */
object FastparseJs {
  def stringChars(c: Char) = c != '\"' && c != '\\'

  def space[$: P]         = P( CharsWhileIn(" \r\n", 0) )
  def digits[$: P]        = P( CharsWhileIn("0-9") )
  def exponent[$: P]      = P( CharIn("eE") ~ CharIn("+\\-").? ~ digits )
  def fractional[$: P]    = P( "." ~ digits )
  def integral[$: P]      = P( "0" | CharIn("1-9")  ~ digits.? )

  def number[$: P] = P(  CharIn("+\\-").? ~ integral ~ fractional.? ~ exponent.? ).!.map(
    x => Js.Num(x.toDouble)
  )

  def `null`[$: P]        = P( "null" ).map(_ => Js.Null)
  def `false`[$: P]       = P( "false" ).map(_ => Js.False)
  def `true`[$: P]        = P( "true" ).map(_ => Js.True)

  def hexDigit[$: P]      = P( CharIn("0-9a-fA-F") )
  def unicodeEscape[$: P] = P( "u" ~ hexDigit ~ hexDigit ~ hexDigit ~ hexDigit )
  def escape[$: P]        = P( "\\" ~ (CharIn("\"/\\\\bfnrt") | unicodeEscape) )

  def strChars[$: P] = P( CharsWhile(stringChars) )
  def string[$: P] =
    P( space ~ "\"" ~/ (strChars | escape).rep.! ~ "\"").map(Js.Str.apply)

  def array[$: P] =
    P( "[" ~/ jsonExpr.rep(sep=","./) ~ space ~ "]").map(Js.Arr(_))

  def pair[$: P] = P( string.map(_.value) ~/ ":" ~/ jsonExpr )

  def obj[$: P] =
    P( "{" ~/ pair.rep(sep=","./) ~ space ~ "}").map(Js.Obj(_))

  def jsonExpr[$: P]: P[Js.Val] = P(
    space ~ (obj | array | string | `true` | `false` | `null` | number) ~ space
  )

  /** A whole document. */
  def document[$: P]: P[Js.Val] = P(jsonExpr ~ End)

  def parseDocument(input: String): Option[Js.Val] = {
    fastparse.parse(input, document(using _)) match {
      case Parsed.Success(value, _) => Some(value)
      case _: Parsed.Failure        => None
    }
  }
}
