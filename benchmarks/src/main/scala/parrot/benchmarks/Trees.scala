package parrot
package benchmarks

import json.JsonGrammar.*

/** The trees of the ports in Parrot's types, for checking that each builds Parrot's tree: their Lists and Seqs become
  * Vectors, and fastparse's flat tuple of a number becomes Parrot's nested one.
  */
object Trees {
  private type Value = JsonObj | JsonArray | JsonString | String | JsonNumber

  def toParrot(x: Any): Any = {
    x match {
      case j: Parboiled2Json.Json => JsonJson(toParrot(j.json).asInstanceOf[Value])
      case j: FastparseJson.Json  => JsonJson(toParrot(j.json).asInstanceOf[Value])
      case j: CatsParseJson.Json  => JsonJson(toParrot(j.json).asInstanceOf[Value])
      case j: ParsleyJson.Json    => JsonJson(toParrot(j.json).asInstanceOf[Value])
      case (m, i, f, e)           => (((toParrot(m), toParrot(i)), toParrot(f)), toParrot(e))
      case (a, b)                 => (toParrot(a), toParrot(b))
      case xs: Seq[?]             => xs.map(toParrot).toVector
      case o: Option[?]           => o.map(toParrot)
      case other                  => other
    }
  }
}
