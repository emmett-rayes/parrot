package parrot
package parser

import scala.util.control.NoStackTrace
import scala.util.matching.Regex
import scala.util.{Failure, Success, Try}

/** The reference interpreter of [[ParserAlgebra]]: the specification against which other interpreters are checked.
  *
  * A concrete [[KleisliParser]] over `String` inputs that collects repetitions into `Vector`.
  */
trait ReferenceParser extends KleisliParser {

  /** The input: a `source` and the current `offset` into it. */
  final case class Input(source: String, offset: Int)

  /** Parse error at `offset` with expected message. */
  final case class ParseError(offset: Int)(expected: => String) extends Exception with NoStackTrace {
    override def getMessage: String = s"expected $expected at position $offset"
  }

  type Many = Vector

  override def nil[B]: Unit => Vector[B] = _ => Vector.empty

  override def snoc[B]: ((Vector[B], B)) => Vector[B] = (bs, b) => bs :+ b

  override def rule[A, B](self: P[A, B], label: String): P[A, B] = {
    a => in =>
      {
        self(a)(in) match {
          case Failure(ParseError(offset)) if offset == in.offset =>
            Failure(ParseError(offset)(label))
          case result => result
        }
      }
  }

  override def literal(expected: String): P[Unit, String] = {
    _ => in =>
      {
        if in.source.startsWith(expected, in.offset) then
          Success((result = expected, state = Input(in.source, in.offset + expected.length)))
        else Failure(ParseError(in.offset)(s"\"$expected\""))
      }
  }

  override def regex(expected: Regex): P[Unit, String] = {
    _ => in =>
      {
        val matcher = expected.pattern.matcher(in.source).region(in.offset, in.source.length)
        if matcher.lookingAt() then
          Success((result = matcher.group(), state = Input(in.source, matcher.end())))
        else Failure(ParseError(in.offset)(s"/${expected.regex}/"))
      }
  }

  extension [B](self: P[Unit, B])
    /** Runs `self` on a prefix of `source`. */
    def parse(source: String): Try[(result: B, offset: Int)] = {
      self(())(Input(source, 0)).map((result, state) => (result = result, offset = state.offset))
    }

  extension [B](self: P[Unit, B])
    /** Runs `self` on the whole of `source`. */
    def parseAll(source: String): Try[(result: B, offset: Int)] = {
      self(())(Input(source, 0)).flatMap { (result, state) =>
        if state.offset == state.source.length then Success((result = result, offset = state.offset))
        else Failure(ParseError(state.offset)("end of input"))
      }
    }
}
