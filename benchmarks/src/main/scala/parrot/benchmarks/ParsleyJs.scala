package parrot
package benchmarks

import parsley.Parsley
import parsley.Parsley.{atomic, eof, many, some}
import parsley.character.{char, oneOf, satisfy, string}
import parsley.combinator.{option, sepBy}

/** fastparse's documented JSON grammar ([[FastparseJs]]) ported to Parsley, into [[Js]]: `span` for fastparse's `.!`.
  * Where fastparse backtracks without a cut, at the first element of an array and the first member of an object, which
  * begin with optional space, the element and the member are `atomic`.
  */
object ParsleyJs {
  private def isDigit(c: Char): Boolean = c >= '0' && c <= '9'
  private def isHex(c: Char): Boolean   = isDigit(c) || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

  val space: Parsley[Unit]      = many(oneOf(' ', '\r', '\n')).void
  val digits: Parsley[Unit]     = some(satisfy(isDigit)).void
  val exponent: Parsley[Unit]   = oneOf('e', 'E') *> option(oneOf('+', '-')) *> digits
  val fractional: Parsley[Unit] = char('.') *> digits
  val integral: Parsley[Unit]   = char('0').void | (satisfy(c => c >= '1' && c <= '9') *> option(digits)).void

  val number: Parsley[Js.Val] = {
    (option(oneOf('+', '-')) *> integral *> option(fractional) *> option(exponent)).span.map(x => Js.Num(x.toDouble))
  }

  val jsonNull: Parsley[Js.Val]  = string("null").as(Js.Null)
  val jsonFalse: Parsley[Js.Val] = string("false").as(Js.False)
  val jsonTrue: Parsley[Js.Val]  = string("true").as(Js.True)

  private val hexDigit             = satisfy(isHex)
  val unicodeEscape: Parsley[Unit] = (char('u') *> hexDigit *> hexDigit *> hexDigit *> hexDigit).void
  val escape: Parsley[Unit]        = char('\\') *> (oneOf('"', '/', '\\', 'b', 'f', 'n', 'r', 't').void | unicodeEscape)

  val strChars: Parsley[Unit] = some(satisfy(c => c != '"' && c != '\\')).void

  /** The text of a string, without its quotes. */
  val jsonString: Parsley[String] = space *> char('"') *> many(strChars | escape).span <* char('"')

  lazy val jsonExpr: Parsley[Js.Val] = {
    val array = (char('[') ~> (sepBy(atomic(jsonExpr), char(',')) <~ space <~ char(']'))).map(Js.Arr(_))
    val pair  = (jsonString <~ char(':')) <~> jsonExpr
    val obj   = (char('{') ~> (sepBy(atomic(pair), char(',')) <~ space <~ char('}'))).map(Js.Obj(_))
    val str   = jsonString.map(Js.Str(_))
    space ~> ((obj: Parsley[Js.Val]) | array | str | jsonTrue | jsonFalse | jsonNull | number) <~ space
  }

  /** A whole document. */
  val document: Parsley[Js.Val] = jsonExpr <~ eof

  def parseDocument(input: String): Option[Js.Val] = document.parse(input).toOption
}
