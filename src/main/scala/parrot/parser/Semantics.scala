package parrot
package parser

import category.*

import scala.util.Try

/** A semantics on a parser algebra **A**.
  *
  * Represents what the parsers of **A** mean and how they are run, where
  *   - [[denote]] sends a parser to its meaning, a parser of [[ReferenceParser]]
  *   - [[diagnose]] and [[run]] evaluate that meaning at a position in a source
  *   - [[parse]] and [[parseAll]] run a parser that takes no semantic input
  *
  * An interpreter implements [[denote]] and may override [[run]] with a faster implementation as long as it respects
  * the same equation. See [[SemanticsLaws]].
  *
  * @note Running is not an operation of **A**, so a grammar, which takes only the algebra, cannot run its parsers.
  *
  * @note Parsers are told apart at every position, not only at the start of a source: a regular expression sees the
  *   input before its position, so `regex("^b".r)` and `literal("b")` do the same at the start of every source and
  *   differ after any other parser that consumes input.
  */
abstract class Semantics(tracked val algebra: ParserAlgebra) extends caps.Pure {
  import algebra.P
  import ReferenceParser.Input

  /** The meaning of `p`: a function from semantic input and the state of a parse to what was expected where it failed
    * furthest, and its result and the state after it, if it succeeds.
    */
  def denote[A, B](p: P[A, B]): A -> Input -> (Expected, Option[(B, Input)])

  /** Runs `p` on semantic input `a` at `offset` in `source`: what it expected where it failed furthest, and its result
    * and the offset after it, if it succeeds.
    */
  def diagnose[A, B](p: P[A, B])(a: A, source: String, offset: Int = 0): (Expected, Option[(B, Int)]) = {
    val (expected, result) = denote(p)(a)(Input(source, offset))
    (expected, result.map((b, in) => (b, in.offset)))
  }

  /** Runs `p` on semantic input `a` at `offset` in `source`: its result and the offset after it, if it succeeds. */
  def run[A, B](p: P[A, B])(a: A, source: String, offset: Int = 0): Option[(B, Int)] = {
    diagnose(p)(a, source, offset)._2
  }

  extension [B](p: P[Unit, B]) {

    /** Runs `p` on a prefix of `source`, reporting what was expected where it failed furthest if it fails. */
    def parse(source: String): Try[(result: B, offset: Int)] = {
      run(p)((), source) match {
        case Some((result, offset)) => scala.util.Success((result = result, offset = offset))
        case scala.None             => scala.util.Failure(ParseError(diagnose(p)((), source)._1))
      }
    }

    /** Runs `p` on the whole of `source`. */
    def parseAll(source: String): Try[(result: B, offset: Int)] = {
      run(p)((), source) match {
        case Some((result, offset)) if offset == source.length =>
          scala.util.Success((result = result, offset = offset))
        case Some((_, offset)) =>
          scala.util.Failure(ParseError(diagnose(p)((), source)._1.join(Expected.at(offset, "end of input"))))
        case scala.None => scala.util.Failure(ParseError(diagnose(p)((), source)._1))
      }
    }
  }

  /** The equation of a semantics: [[run]] is [[diagnose]] without the report. */
  object SemanticsLaws {

    /** *run*(*p*)(*a*,*s*,*o*) = *π*₂(*diagnose*(*p*)(*a*,*s*,*o*)) */
    def runDefinition[A, B](p: P[A, B])(a: A, source: String, offset: Int)(
      using Option[(B, Int)] is Observable
    ): Boolean = {
      run(p)(a, source, offset) =?= diagnose(p)(a, source, offset)._2
    }
  }
}

/** A parse failure, reported as what was expected where it failed furthest.
  *
  * A parse can fail without expecting anything, for instance at a failure or at a negation whose parser succeeded,
  * since those are silent. Its diagnostics are then ⊥, and it is reported as a failure at the start.
  */
final case class ParseError(expected: Expected) extends Exception with scala.util.control.NoStackTrace {

  /** The furthest position at which something failed, or the start if nothing was expected. */
  def offset: Int = expected.position.max(0)

  override def getMessage: String = {
    if expected.expectations.isEmpty then s"no parse at position $offset"
    else s"expected ${expected.describe} at position $offset"
  }
}
