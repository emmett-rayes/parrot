package parrot

/** The JSON grammar. */
final class JsonGrammar[P[_, _]: ParserAlgebra] {
  import JsonGrammar.*

  val algebra = summon[P is ParserAlgebra]
  import algebra.{*, given}

  /** A parser that consumes JSON whitespace. */
  val s: P[Unit, JsonS] = {
    regex("[ \t\n\r]+".r)
  }

  /** A parser that consumes the literal "true". */
  val jsonTrue: P[Unit, JsonTrue] = {
    literal("true").rmap(identity)
  }

  /** A parser that consumes the literal "false". */
  val jsonFalse: P[Unit, JsonFalse] = {
    literal("false").rmap(identity)
  }

  /** A parser that consumes the literal "null". */
  val jsonNull: P[Unit, JsonNull] = {
    literal("null").rmap(identity)
  }

  /** A parser that consumes a minus sign "-". */
  val minus: P[Unit, JsonMinus] = {
    literal("-").rmap(identity)
  }

  /** A parser that consumes the integral part of a JSON number. */
  val integralPart: P[Unit, JsonIntegralPart] = {
    literal("0").rmap(identity) +> regex("[1-9][0-9]*".r)
  }

  /** A parser that consumes the fractional part of a JSON number. */
  val fractionalPart: P[Unit, JsonFractionalPart] = {
    literal(".") *> regex("[0-9]+".r)
  }

  /** A parser that consumes the exponent part of a JSON number. */
  val exponentPart: P[Unit, JsonExponentPart] = {
    (regex("[eE]".r) *> regex("[-+]".r).optional) && regex("[0-9]+".r)
  }

  /** A parser that consumes a JSON number. */
  val number: P[Unit, JsonNumber] = {
    minus.optional
    && integralPart
    && fractionalPart.optional
    && exponentPart.optional
  }

  /** A parser that consumes a four-digit hexadecimal Unicode escape sequence. */
  val unicodeEscape: P[Unit, JsonUnicodeEscape] = {
    literal("u") *> regex("[0-9A-Fa-f]".r).times(4)
  }

  /** A parser that consumes a JSON escape sequence. */
  val escape: P[Unit, JsonEscape] = {
    val simple = regex("[\"/\\\\bfnrt]".r)
    literal("\\") *> simple.union(unicodeEscape)
  }

  /** A parser that consumes a JSON string literal. */
  val string: P[Unit, JsonString] = {
    val unescaped = regex("[^\"\\\\\\u0000-\\u001f]".r)
    val character = unescaped.union(escape)
    val quoted    = literal("\"") *> character.repeated >* literal("\"")
    s.optional *> quoted >* s.optional
  }

  /** The start symbol of the JSON grammar along with mutually recursive object and array parsers. */
  val (json, obj, array): (P[Unit, JsonJson], P[Unit, JsonObj], P[Unit, JsonArray]) = {
    algebra.recursive[(P[Unit, JsonJson], P[Unit, JsonObj], P[Unit, JsonArray])] { (recJson, recObj, recArray) =>
      /** A parser that consumes a JSON object. */
      val obj = {
        val member = (string >* literal(":")) && recJson
        val body   = member.separatedBy(literal(",")).union(s.optional)
        literal("{") *> body >* literal("}")
      }

      /** A parser that consumes a JSON array. */
      val array = {
        val body = recJson.separatedBy(literal(",")).union(s.optional)
        literal("[") *> body >* literal("]")
      }

      /** A parser that consumes any valid JSON value. */
      val json = {
        val value = obj
          .union(array)
          .union(string)
          .union(jsonTrue)
          .union(jsonFalse)
          .union(jsonNull)
          .union(number)
        (s.optional *> value >* s.optional).rmap(JsonJson(_))
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
  type JsonUnicodeEscape = List[String]
  type JsonEscape        = String | JsonUnicodeEscape
  type JsonString        = List[String | JsonEscape]
  type JsonObj           = List[(JsonString, JsonJson)] | Option[JsonS]
  type JsonArray         = List[JsonJson] | Option[JsonS]

  /** Creates a `JsonGrammar` using the given `ParserAlgebra`. */
  def apply[P[_, _]: ParserAlgebra]: JsonGrammar[P] = {
    new JsonGrammar[P]
  }

  /** Fixpoint wrapper to break the recursion of type aliases. */
  case class JsonJson(json: JsonObj | JsonArray | JsonString | JsonTrue | JsonFalse | JsonNull | JsonNumber)
}
