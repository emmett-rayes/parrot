package parrot
package benchmarks

import cats.parse.{Parser as P, Parser0 as P0}

/** fastparse's documented JSON grammar ([[FastparseJs]]) ported to cats-parse, into [[Js]]: `.string` for fastparse's
  * `.!`. Where fastparse backtracks without a cut, at the first element of an array and the first member of an object,
  * which begin with optional space, the element and the member `backtrack`.
  */
object CatsParseJs {
  private def isDigit(c: Char): Boolean = c >= '0' && c <= '9'

  val space: P0[Unit]     = P.charsWhile0(c => c == ' ' || c == '\r' || c == '\n').void
  val digits: P[Unit]     = P.charsWhile(isDigit).void
  val exponent: P[Unit]   = P.charIn('e', 'E') *> P.charIn('+', '-').? *> digits
  val fractional: P[Unit] = P.char('.') *> digits
  val integral: P[Unit]   = P.char('0') | (P.charIn('1' to '9') *> digits.?).void

  val number: P[Js.Val] = {
    (P.charIn('+', '-').?.with1 *> integral *> fractional.? *> exponent.?).string.map(x => Js.Num(x.toDouble))
  }

  val jsonNull: P[Js.Val]  = P.string("null").as(Js.Null)
  val jsonFalse: P[Js.Val] = P.string("false").as(Js.False)
  val jsonTrue: P[Js.Val]  = P.string("true").as(Js.True)

  private val hexDigit       = P.charIn(('0' to '9') ++ ('a' to 'f') ++ ('A' to 'F')).void
  val unicodeEscape: P[Unit] = P.char('u') *> hexDigit *> hexDigit *> hexDigit *> hexDigit
  val escape: P[Unit]        = P.char('\\') *> (P.charIn("\"/\\bfnrt".toList).void | unicodeEscape)

  val strChars: P[Unit] = P.charsWhile(c => c != '"' && c != '\\').void

  /** The text of a string, without its quotes. */
  val string: P[String] = space.with1 *> P.char('"') *> (strChars | escape).rep0.string <* P.char('"')

  val jsonExpr: P[Js.Val] = P.recursive[Js.Val] { jsonExpr =>
    val array = (P.char('[') *> jsonExpr.backtrack.repSep0(P.char(',')) <* space <* P.char(']')).map(Js.Arr(_))
    val pair  = (string <* P.char(':')) ~ jsonExpr
    val obj   = (P.char('{') *> pair.backtrack.repSep0(P.char(',')) <* space <* P.char('}')).map(Js.Obj(_))
    val str   = string.map(Js.Str(_))
    space.with1 *> ((obj: P[Js.Val]) | array | str | jsonTrue | jsonFalse | jsonNull | number) <* space
  }

  def parseDocument(input: String): Option[Js.Val] = jsonExpr.parseAll(input).toOption
}
