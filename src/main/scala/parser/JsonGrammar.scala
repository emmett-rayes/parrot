package parrot
package parser

import category.Profunctor.on
import category.Promonad

/** The JSON grammar, ported from the legacy interpreter.
  *
  * It is written once against any [[ParserAlgebra.Standard]] algebra whose pure functions embed Scala functions, i.e.
  * whose `On` is a promonad on `Function`, so the same grammar runs on every interpreter.
  */
final class JsonGrammar(tracked val algebra: ParserAlgebra.Standard)(using Lift: algebra.On is Promonad on Function) {
  import JsonGrammar.*
  import algebra.*

  def lift[A, B](f: A => B): A ==> B = Lift.unit(f)

  extension [A, B](self: P[A, B])
    /** Tries `self`, returning `Some` on success or `None` on failure. */
    private def opt: P[A, Option[B]] = self.map(lift[B, Option[B]](Some(_))) |>
      pure(lift[A, Option[B]](_ => scala.None))

    /** Tries `self`, falling back to `other`, into the union of their results. */
    private def union[C](other: P[A, C]): P[A, B | C] = self.map(lift[B, B | C](b => b)) |>
      other.map(lift[C, B | C](c => c))

  /** A parser that consumes JSON whitespace. */
  val s: P[Unit, JsonS] = regex("[ \t\n\r]+".r)

  /** A parser that consumes the literal "true". */
  val jsonTrue: P[Unit, JsonTrue] = literal("true")

  /** A parser that consumes the literal "false". */
  val jsonFalse: P[Unit, JsonFalse] = literal("false")

  /** A parser that consumes the literal "null". */
  val jsonNull: P[Unit, JsonNull] = literal("null")

  /** A parser that consumes a minus sign "-". */
  val minus: P[Unit, JsonMinus] = literal("-")

  /** A parser that consumes the integral part of a JSON number. */
  val integralPart: P[Unit, JsonIntegralPart] = literal("0") |> regex("[1-9][0-9]*".r)

  /** A parser that consumes the fractional part of a JSON number. */
  val fractionalPart: P[Unit, JsonFractionalPart] = literal(".") *> regex("[0-9]+".r)

  /** A parser that consumes the exponent part of a JSON number. */
  val exponentPart: P[Unit, JsonExponentPart] = (regex("[eE]".r) *> regex("[-+]".r).opt) && regex("[0-9]+".r)

  /** A parser that consumes a JSON number. */
  val number: P[Unit, JsonNumber] = minus.opt && integralPart && fractionalPart.opt && exponentPart.opt

  /** A parser that consumes a four-digit hexadecimal Unicode escape sequence. */
  val unicodeEscape: P[Unit, JsonUnicodeEscape] = literal("u") *> regex("[0-9A-Fa-f]".r).times(4)

  /** A parser that consumes a JSON escape sequence. */
  val escape: P[Unit, JsonEscape] = literal("\\") *> regex("[\"/\\\\bfnrt]".r).union(unicodeEscape)

  /** A parser that consumes a JSON string literal. */
  val string: P[Unit, JsonString] = {
    val unescaped = regex("[^\"\\\\\\u0000-\\u001f]+".r)
    val character = unescaped.union(escape)
    val quoted    = literal("\"") *> character.repeated <* literal("\"")
    s.opt *> quoted <* s.opt
  }

  /** The start symbol of the JSON grammar along with the mutually recursive object and array parsers. */
  val (json, obj, array) = {
    recursive[(P[Unit, JsonJson], P[Unit, JsonObj], P[Unit, JsonArray])] { (recJson, _, _) =>
      /** A parser that consumes a JSON object. */
      val obj = {
        val member = (string <* literal(":")) && recJson
        val body   = member.separatedBy(literal(",")).union(s.opt)
        literal("{") *> body <* literal("}")
      }

      /** A parser that consumes a JSON array. */
      val array = {
        val body = recJson.separatedBy(literal(",")).union(s.opt)
        literal("[") *> body <* literal("]")
      }

      /** A parser that consumes any valid JSON value. */
      val json = {
        val value = obj.union(array).union(string).union(jsonTrue).union(jsonFalse).union(jsonNull).union(number)
        (s.opt *> value <* s.opt).map(lift(JsonJson(_)))
      }

      (json, obj, array)
    }
  }
}

object JsonGrammar {

  /** Aliases for the compound result types of the JSON nonterminals. */
  type JsonS              = String
  type JsonTrue           = String
  type JsonFalse          = String
  type JsonNull           = String
  type JsonMinus          = String
  type JsonIntegralPart   = String
  type JsonFractionalPart = String
  type JsonExponentPart   = (Option[String], String)
  type JsonNumber = (((Option[JsonMinus], JsonIntegralPart), Option[JsonFractionalPart]), Option[JsonExponentPart])
  type JsonUnicodeEscape = Vector[String]
  type JsonEscape        = String | JsonUnicodeEscape
  type JsonString        = Vector[String | JsonEscape]
  type JsonObj           = Vector[(JsonString, JsonJson)] | Option[JsonS]
  type JsonArray         = Vector[JsonJson] | Option[JsonS]

  /** Fixpoint wrapper to break the recursion of type aliases. */
  final case class JsonJson(json: JsonObj | JsonArray | JsonString | JsonTrue | JsonFalse | JsonNull | JsonNumber)
}
