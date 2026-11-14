package parrot
package benchmarks

import parser.ParserAlgebra

/** fastparse's documented JSON grammar ([[FastparseJs]]) ported to Parrot, into [[Js]]: `capture` for fastparse's `.!`.
  * Parrot's choice backtracks like PEG's, which accepts the same documents as fastparse's cuts here.
  */
final class ParrotJs(tracked val algebra: ParserAlgebra) {
  import algebra.*

  private val space: P[Unit, String]      = regex("[ \r\n]*".r)
  private val digits: P[Unit, String]     = regex("[0-9]+".r)
  private val exponent: P[Unit, String]   = regex("[eE][+-]?[0-9]+".r)
  private val fractional: P[Unit, String] = literal(".") *> digits
  private val integral: P[Unit, String]   = literal("0") |> regex("[1-9][0-9]*".r)

  private val number: P[Unit, Js.Val] = {
    (regex("[+-]".r).option && integral && fractional.option && exponent.option).capture.map(
      lift[String, Js.Val](x => Js.Num(x.toDouble))
    )
  }

  private val jsonNull: P[Unit, Js.Val]  = literal("null").map(lift[String, Js.Val](_ => Js.Null))
  private val jsonFalse: P[Unit, Js.Val] = literal("false").map(lift[String, Js.Val](_ => Js.False))
  private val jsonTrue: P[Unit, Js.Val]  = literal("true").map(lift[String, Js.Val](_ => Js.True))

  private val unicodeEscape: P[Unit, String] = regex("u[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F]".r)
  private val escape: P[Unit, String]        = literal("\\") *> (regex("[\"/\\\\bfnrt]".r) |> unicodeEscape)

  private val strChars: P[Unit, String] = regex("[^\"\\\\]+".r)

  /** The text of a string, without its quotes. */
  private val string: P[Unit, String] = {
    space *> literal("\"") *> (strChars |> escape).repeated.capture <* literal("\"")
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
