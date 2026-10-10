package parrot
package parser

import parrot.category.{Cartesian, Cocartesian, Kleisli, Monad}

import scala.util.matching.Regex

/** The reference interpreter of [[ParserAlgebra]]: the specification against which other interpreters are checked.
  *
  * Parsers are the Kleisli arrows `A => Parse[B]` of the [[Parse]] monad, a deterministic, backtracking computation
  * over the input. The Kleisli construction lifts the structure of the monad to all the structural mixins, so this
  * interpreter only implements the lexical primitives and recursion; every other operation comes from the generic
  * mixins and is therefore tested along with it.
  *
  * Fixed points are naive unfoldings, so left-recursive grammars diverge, as do repetitions of parsers that succeed
  * without consuming input.
  *
  * @note
  *   Parsers are plain functions, so on concrete parsers `p.andThen(q)` and `p.compose(q)` resolve to the members of
  *   `Function1`. Use `p >> q` instead.
  */
object ReferenceParser
    extends ParserAlgebra,
      ParserAlgebra.Sequencing,
      ParserAlgebra.Zipping,
      ParserAlgebra.Branching,
      ParserAlgebra.Alternation,
      ParserAlgebra.Lookahead,
      ParserAlgebra.Looping,
      ParserAlgebra.Pairing,
      ParserAlgebra.Iteration {

  /** The input: a `source` and the current `offset` into it. */
  final case class Input(source: String, offset: Int)

  /** The outcome of running a parser. */
  enum Result[+B] derives CanEqual {

    /** Success with a semantic `value`, having consumed the input up to `offset`. */
    case Success(value: B, offset: Int)

    /** Failure at `offset`, expecting `expected`. */
    case Failure(offset: Int, expected: String) extends Result[Nothing]
  }

  import Result.{Failure, Success}

  /** The parse monad: a computation over the [[Input]] that either fails or yields a value and a new offset. */
  type Parse[B] = Input => Result[B]

  /** `Parse` is a monad with backtracking ordered choice, lookahead and iteration. */
  object ParseIsMonad extends Monad.Plus, Monad.Restriction, Monad.Elgot {
    type Self[B] = Parse[B]

    def unit[A](a: A): Parse[A] = in => Success(a, in.offset)

    def zero[A]: Parse[A] = in => Failure(in.offset, "failure")

    extension [A](m: Parse[A])
      def flatMap[B](f: A => Parse[B]): Parse[B] = in => {
        m(in) match {
          case Success(a, offset) => f(a)(in.copy(offset = offset))
          case failed: Failure    => failed
        }
      }

      /** Tries `m`, backtracking to `n` on failure; of two failures keeps the one that got furthest. */
      def plus(n: Parse[A]): Parse[A] = in => {
        m(in) match {
          case success: Success[A] => success
          case left: Failure       =>
            n(in) match {
              case success: Success[A] => success
              case right: Failure      => if right.offset > left.offset then right else left
            }
        }
      }

      def restrict: Parse[Unit] = in => {
        m(in) match {
          case Success(_, _)   => Success((), in.offset)
          case failed: Failure => failed
        }
      }

    def iterate[A, B](f: A => Parse[Either[B, A]]): A => Parse[B] = a =>
      in => {
        @annotation.tailrec
        def go(a: A, offset: Int): Result[B] = f(a)(in.copy(offset = offset)) match {
          case Success(Left(b), next)  => Success(b, next)
          case Success(Right(a), next) => go(a, next)
          case failed: Failure         => failed
        }
        go(a, in.offset)
      }
  }

  type Self[A, B]        = Kleisli[Parse][A, B]
  type On[A, B]          = Function[A, B]
  type Empty             = Unit
  type Pair[A, B]        = (A, B)
  type None              = Nothing
  type Alternative[A, B] = Either[A, B]
  type Many[B]           = Vector[B]

  override val SelfIsPromonad    = Kleisli.KleisliIsPromonad[Parse](using ParseIsMonad)
  override val SelfIsStrong      = Kleisli.KleisliIsStrong[Parse](using ParseIsMonad)
  override val SelfIsCocartesian = Kleisli.KleisliIsCocartesian[Parse](using ParseIsMonad)
  override val SelfIsEnriched    = Kleisli.KleisliIsEnriched[Parse](using ParseIsMonad)
  override val SelfIsRestriction = Kleisli.KleisliIsRestriction[Parse](using ParseIsMonad)
  override val SelfIsElgot       = Kleisli.KleisliIsElgot[Parse](using ParseIsMonad)

  override val OnIsCartesian: Cartesian.FunctionIsCartesian.type       = Cartesian.FunctionIsCartesian
  override val OnIsCocartesian: Cocartesian.FunctionIsCocartesian.type = Cocartesian.FunctionIsCocartesian

  override def nil[B]: Unit => Vector[B] = _ => Vector.empty

  override def snoc[B]: ((Vector[B], B)) => Vector[B] = (bs, b) => bs :+ b

  extension [B](self: P[Unit, B])
    /** Runs `self` on a prefix of `source`. */
    def parse(source: String): Result[B] = self(())(Input(source, 0))

    /** Runs `self` on the whole of `source`. */
    def parseAll(source: String): Result[B] = self.thenSkip(regex("(?s).".r).not).parse(source)

  // ===========================================================================
  // Interpreter-specific primitives
  // ===========================================================================

  extension [A, B](self: P[A, B])
    override def rule(label: String): P[A, B] = a =>
      in => {
        self(a)(in) match {
          case Failure(at, _) if at == in.offset => Failure(at, label)
          case result                            => result
        }
      }

  override def literal(expected: String): P[Unit, String] = _ =>
    in => {
      if in.source.startsWith(expected, in.offset) then Success(expected, in.offset + expected.length)
      else Failure(in.offset, s"\"$expected\"")
    }

  override def regex(expected: Regex): P[Unit, String] = _ =>
    in => {
      val matcher = expected.pattern.matcher(in.source).region(in.offset, in.source.length)
      if matcher.lookingAt() then Success(matcher.group(), matcher.end())
      else Failure(in.offset, s"/${expected.regex}/")
    }

  override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = {
    lazy val fixed: P[A, B] = f(a => fixed(a))
    fixed
  }
}
