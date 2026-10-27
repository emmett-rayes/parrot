package parrot
package parser

import category.*

import scala.util.matching.Regex

/** The reference interpreter of [[ParserAlgebra]]: the specification against which other interpreters are checked.
  *
  * A parser is a Kleisli arrow of a monad built from the library's transformers: the state transformer over the failure
  * transformer over the writer of [[Expected]], so `P[A, B]` = `A -> Input -> (Expected, Option[(B, Input)])`. Every
  * structure is derived from that monad: backtracking choice and silent lookahead from the classical structure
  * [[ReferenceParser.Silent]] lifted through the state, iteration and recursion guarded by the length of the remaining
  * input. It is slow and not stack-safe on deep nesting; it is meant to be obviously right.
  */
class ReferenceParser
    extends ParserAlgebra(
      ReferenceParser.Arrows,
      Total.Product,
      Total.Coproduct,
      ReferenceParser.Zipping,
      ReferenceParser.Branching,
      ReferenceParser.Choice,
      ReferenceParser.Loops,
      ReferenceParser.Knots,
    ) {
  import ReferenceParser.Input

  def lift[A, B](f: A -> B): A -> B = {
    f
  }

  def rule[A, B](
    p: A -> Input -> (Expected, Option[(B, Input)]),
    label: String,
  ): A -> Input -> (Expected, Option[(B, Input)]) = {
    a => in =>
      val (expected, result) = p(a)(in)
      val relabeled          =
        if result.isEmpty && expected.position <= in.offset then Expected.at(in.offset, label)
        else expected.tag(label)
      (relabeled, result)
  }

  def literal(expected: String): Unit -> Input -> (Expected, Option[(String, Input)]) = {
    _ => in =>
      if in.source.startsWith(expected, in.offset) then
        (Expected.bottom, Some((expected, Input(in.source, in.offset + expected.length))))
      else (Expected.at(in.offset, s"\"$expected\""), None)
  }

  def regex(expected: Regex): Unit -> Input -> (Expected, Option[(String, Input)]) = {
    _ => in =>
      val end = Scanner.matchAt(expected, in.source, in.offset)
      if end < 0 then (Expected.at(in.offset, s"/${expected.regex}/"), None)
      else (Expected.bottom, Some((in.source.substring(in.offset, end).nn, Input(in.source, end))))
  }

  def diagnose[A, B](
    p: A -> Input -> (Expected, Option[(B, Input)])
  )(a: A, source: String): (Expected, Option[(B, Int)]) = {
    val (expected, result) = p(a)(Input(source, 0))
    (expected, result.map((b, in) => (b, in.offset)))
  }
}

object ReferenceParser {

  /** The state of a parse: the `source` and the current `offset` into it. */
  final case class Input(source: String, offset: Int)

  /** Guarded loops and recursion must consume input: the measure of a state is the length of the remaining input. */
  given InputIsMeasure: Input is Measure {
    def measure(in: Input): Int = in.source.length - in.offset
  }

  /** Diagnostics are a writer effect: what was expected, joined in the semilattice of [[Expected]]. */
  object Diagnostics extends Writer(Expected.Furthest)

  /** Outcomes of a parse step: diagnostics, and a result or a failure. */
  object Outcome extends OptionT(Diagnostics)

  /** The classical structure of outcomes, with silent tests, where
    *   - 0 = (⊥,none): failure reports nothing
    *   - *m̄* and *m̄*ᶜ test *m* but report nothing about it: lookahead and negation are silent
    *   - *m* ⊳ *n* reports what *m* expected and, where *m* fails, also what *n* expected
    *
    * With this structure **R2**, **R3** and the laws of zero and complement hold exactly, and **R1** and **R4** up to
    * diagnostics (see [[ParserAlgebra.ParserLaws]]). Keeping the diagnostics of tests, as [[OptionT.ClassicalOf]] does,
    * would make **R1** and **R4** exact but break **R2** and the laws of zero and complement.
    */
  object Silent extends ClassicalMonad(Outcome) {

    def restrict[A](m: (Expected, Option[A])): (Expected, Option[Unit]) = {
      (Expected.bottom, m._2.map(_ => ()))
    }

    def zero[A]: (Expected, Option[A]) = {
      (Expected.bottom, None)
    }

    def complement[A](m: (Expected, Option[A])): (Expected, Option[Unit]) = {
      (Expected.bottom, if m._2.isEmpty then Some(()) else None)
    }

    def orElse[A](m: (Expected, Option[A]), n: -> (Expected, Option[A])): (Expected, Option[A]) = {
      if m._2.nonEmpty then m
      else {
        val (expected, result) = n
        (m._1.join(expected), result)
      }
    }

    override def attempt[A](m: (Expected, Option[A])): (Expected, Option[Option[A]]) = {
      (m._1, Some(m._2))
    }
  }

  /** Computations that read the input, report diagnostics and may fail. */
  object State extends StateT[Input](Outcome)

  /** Parsers: the Kleisli arrows of [[State]]. */
  object Arrows extends Kleisli(State)

  /** Failure, backtracking and silent lookahead for [[State]]: [[Silent]], lifted. */
  object Backtracking extends StateT.ClassicalOf(State, Silent)

  /** Failure, lookahead, negation, attempt and ordered choice for parsers. */
  object Choice extends Kleisli.ClassicalOf(Arrows, Backtracking)

  /** Parsers run side by side on pairs. */
  object Zipping extends Kleisli.ProductStrength(Arrows)

  /** Parsers run on one side of a tagged union. */
  object Branching extends Kleisli.CoproductStrength(Arrows)

  /** Loops over [[State]] guarded by consumed input; a step without progress fails silently. */
  object Iteration extends StateT.GuardedIteration(State, Silent)

  /** Guarded iteration of parsers. */
  object Loops extends Kleisli.ElgotOf(Branching, Iteration)

  /** Guarded recursion of parsers; a call without progress fails silently. */
  object Knots extends StateT.GuardedRecursion(Arrows, Silent)
}
