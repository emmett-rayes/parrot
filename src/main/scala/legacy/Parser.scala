package parrot
package legacy

import scala.util.Try

/** LinkedHashMap preserves insertion order, serving as both memo table and rollback log in O(1). */
type ParserState = (memo: java.util.LinkedHashMap[Any, Any], tokens: Tokens)

object ParserState {
  given Ordering[ParserState] = Ordering.by(_.tokens)

  def empty(tokens: Tokens): ParserState = (memo = java.util.LinkedHashMap(), tokens = tokens)
}

/** The result of running a parser: either a failure or a result paired with the remaining state. */
type ParserResult[A] = Try[(result: A, state: ParserState)]

object ParserResult {
  import ParserState.given

  import scala.math.Ordering.Implicits.*
  import scala.util.{Failure, Success}

  /** Parser results are ordered by failure vs success, then by unconsumed tokens in the remaining state. */
  given [A] => Ordering[ParserResult[A]] = Ordering.fromLessThan {
    case (Failure(_), Success(_))          => true
    case (Success(current), Success(next)) => next.state < current.state
    case _                                 => false
  }
}

/** A Parser over `ParserState` input with `Throwable` failures.
  *
  * A parser of type *P*[*A*,*B*] maps an input *A* and a `ParserState` to either a failure or a result *B* paired with
  * the unconsumed remainder of the `ParserState`.
  *
  * Implemented as the Kleisli profunctor of the state monad over the `Try` monad, where
  *   - *P*[*A*,*B*] = *A* → `ParserState` → ((*B* × `ParserState`) + `Throwable`) is the object part
  *   - *P*(*f*,*g*) = *f* ; - ; ((*g* × *id*) + *id*) is the morphism part
  */
type Parser = Kleisli[StateT[ParserState, Try]]

object Parser {
  import Kleisli.given
  import Promonad.given
  import StateT.given

  extension [A, B](self: Parser[A, B])
    /** Runs a parser on a given state and semantic input. */
    def run(a: A, state: ParserState): ParserResult[B] = {
      self(a)(state)
    }

  extension [A, B](self: Parser[A, B])
    /** Runs a parser on a given string and semantic input. */
    def run(a: A, input: String): ParserResult[B] = {
      self.run(a, ParserState.empty(input.asTokens))
    }

  extension [B](self: Parser[Unit, B])
    /** Runs a parser on a given state. */
    def run(state: ParserState): ParserResult[B] = {
      self.run((), state)
    }

  extension [B](self: Parser[Unit, B])
    /** Runs a parser on a given string. */
    def run(input: String): ParserResult[B] = {
      self.run((), ParserState.empty(input.asTokens))
    }

  /** The canonical parser implementation is a parser algebra. */
  given ParserIsCanonicalParser: Parser is CanonicalParser {
    import ParserResult.given

    import scala.math.Ordering.Implicits.*
    import scala.util.chaining.*
    import scala.util.{Failure, Success}

    def literal(expected: String): Parser[Unit, String] = {
      val tokens = expected.asTokens
      _ =>
        state =>
          if state.tokens.startsWith(tokens) then
            Success((result = expected, state = (memo = state.memo, tokens = state.tokens.drop(tokens.length))))
          else
            Failure(ParserError(s"expected $expected at this position: \"${state.tokens.context()}\"."))
    }

    def regex(expected: scala.util.matching.Regex): Parser[Unit, String] = {
      val pattern = expected.pattern
      _ =>
        state => {
          val matcher = pattern.matcher(state.tokens)
          if matcher.lookingAt() then
            val end = matcher.end()
            Success((
              result = state.tokens.substring(0, end),
              state = (memo = state.memo, tokens = state.tokens.drop(end)),
            ))
          else
            Failure(ParserError(s"no matching for ${expected.regex} at this position \"${state.tokens.context()}\"."))
        }
    }

    extension [A, B](self: Parser[A, B])
      def rule(label: String): Parser[A, B] = {
        a => state =>
          {
            val key    = (label, a, state.tokens)
            val cached = state.memo.get(key)
            if cached != null then cached.asInstanceOf[ParserResult[B]]
            else {
              val result = self(a)(state)
              state.memo.put(key, result)
              result
            }
          }
      }

    def recursive[A, B](f: Parser[A, B] => Parser[A, B]): Parser[A, B] = {
      val randomId = scala.util.Random.nextLong().toHexString // per fixpoint calculation unique ID
      val bottom   = Failure(Exception("recursion bottom")): ParserResult[B]

      def parser(headA: A)(head: ParserState): ParserResult[B] = {
        val key  = (randomId, headA, head.tokens)
        val mark = head.memo.size

        var current       = bottom
        var leftRecursive = false

        val self: Parser[A, B] = {
          a => s =>
            if s.tokens == head.tokens && a == headA then {
              leftRecursive = true
              current
            } else parser.rule(randomId)(a)(s)
        }
        val body: Parser[A, B] = f(self)

        def restore(): Unit = {
          while head.memo.size > mark do {
            val _ = head.memo.pollLastEntry()
          }
        }

        @annotation.tailrec
        def iterate(step: Int): ParserResult[B] = {
          step match {
            case 0 => current
            case n =>
              restore()
              head.memo.put(key, current)
              val next = body(headA)(head)
              if current < next then {
                current = next
                iterate(n - 1)
              } else current
          }
        }

        def grow(length: Int): ParserResult[B] = {
          iterate(length).tap(_ => restore())
        }

        head.memo.put(key, bottom)
        val first = body(headA)(head)
        if !leftRecursive then first
        else {
          current = first
          grow(head.tokens.length)
        }
      }

      parser.rule(randomId)
    }
  }
}
