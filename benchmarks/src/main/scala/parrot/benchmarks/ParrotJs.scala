package parrot
package benchmarks

import parser.ParserAlgebra

/** fastparse's documented JSON grammar ([[FastparseJs]]) ported to Parrot, into [[Js]].
  *
  * Parrot has no combinator that returns the input a parser consumed, as fastparse's `.!` does, and its scanner compiles
  * only regular expressions without groups or alternatives. So a token that fastparse captures is the concatenation of
  * what its parts return: a number is parsed from the text of its sign, digits, fraction and exponent, and a string is
  * the text of its runs and escapes.
  */
final class ParrotJs(tracked val algebra: ParserAlgebra) {
  import algebra.*

  private val space: P[Unit, String]      = regex("[ \r\n]*".r)
  private val digits: P[Unit, String]     = regex("[0-9]+".r)
  private val exponent: P[Unit, String]   = regex("[eE][+-]?[0-9]+".r)
  private val fractional: P[Unit, String] = literal(".") *> digits
  private val integral: P[Unit, String]   = literal("0") |> regex("[1-9][0-9]*".r)

  private val number: P[Unit, Js.Val] = {
    (regex("[+-]".r).option && integral && fractional.option && exponent.option).map(
      lift[(((Option[String], String), Option[String]), Option[String]), Js.Val] { case (((sign, int), frac), exp) =>
        Js.Num((sign.getOrElse("") + int + frac.fold("")("." + _) + exp.getOrElse("")).toDouble)
      }
    )
  }

  private val jsonNull: P[Unit, Js.Val]  = literal("null").map(lift[String, Js.Val](_ => Js.Null))
  private val jsonFalse: P[Unit, Js.Val] = literal("false").map(lift[String, Js.Val](_ => Js.False))
  private val jsonTrue: P[Unit, Js.Val]  = literal("true").map(lift[String, Js.Val](_ => Js.True))

  private val unicodeEscape: P[Unit, String] = regex("u[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]".r)
  private val escape: P[Unit, String]        = {
    (literal("\\") && (regex("[\"/\\\\bfnrt]".r) |> unicodeEscape)).map(lift[(String, String), String](_ + _))
  }

  private val strChars: P[Unit, String] = regex("[^\"\\\\]+".r)

  /** The text of a string, without its quotes. */
  private val string: P[Unit, String] = {
    (space *> literal("\"") *> (strChars |> escape).repeated <* literal("\"")).map(lift[Vector[String], String](_.mkString))
  }

  val jsonExpr: P[Unit, Js.Val] = recursive[Unit, Js.Val] { jsonExpr =>
    val array = (literal("[") *> jsonExpr.separatedBy(literal(",")).option <* space <* literal("]")).map(
      lift[Option[Vector[Js.Val]], Js.Val](values => Js.Arr(values.getOrElse(Vector.empty)))
    )
    val pair = string <* literal(":") && jsonExpr
    val obj  = (literal("{") *> pair.separatedBy(literal(",")).option <* space <* literal("}")).map(
      lift[Option[Vector[(String, Js.Val)]], Js.Val](pairs => Js.Obj(pairs.getOrElse(Vector.empty)))
    )
    val str = string.map(lift[String, Js.Val](Js.Str(_)))
    space *> (obj |> array |> str |> jsonTrue |> jsonFalse |> jsonNull |> number) <* space
  }
}
