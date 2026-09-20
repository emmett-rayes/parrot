package parrot

import scala.collection.mutable
import scala.util.Try

/** LinkedHashMap preserves insertion order, serving as both memo table and rollback log in O(1). */
type ParserState = (memo: mutable.LinkedHashMap[Any, Any], tokens: Tokens)

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
    def run(a: A, state: ParserState): Try[(result: B, state: ParserState)] = {
      self(a)(state)
    }

  extension [A, B](self: Parser[A, B])
    /** Runs a parser on a given string and semantic input. */
    def run(a: A, input: String): Try[(result: B, state: ParserState)] = {
      self.run(a, (memo = mutable.LinkedHashMap.empty, tokens = input.asTokens))
    }

  extension [B](self: Parser[Unit, B])
    /** Runs a parser on a given state. */
    def run(state: ParserState): Try[(result: B, state: ParserState)] = {
      self.run((), state)
    }

  extension [B](self: Parser[Unit, B])
    /** Runs a parser on a given string. */
    def run(input: String): Try[(result: B, state: ParserState)] = {
      self.run((), (memo = mutable.LinkedHashMap.empty, tokens = input.asTokens))
    }

  /** The canonical parser implementation is a parser algebra. */
  given ParserIsCanonicalParser: Parser is CanonicalParser {
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
      _ => state =>
        expected.findPrefixMatchOf(state.tokens) match {
          case Some(m) =>
            Success((
              result = state.tokens.substring(m.start, m.end),
              state = (memo = state.memo, tokens = state.tokens.drop(m.end))
            ))
          case None =>
            Failure(
              ParserError(s"no matching for ${expected.regex} at this position \"${state.tokens.context()}\".")
            )
        }
    }

    extension [A, B](self: Parser[A, B])
      def rule(label: String): Parser[A, B] = {
        a => state =>
          val key = (label, a, state.tokens)
          state.memo.get(key) match {
            case Some(cached) =>
              cached.asInstanceOf[Try[(result: B, state: ParserState)]]
            case None =>
              self(a)(state).tap(state.memo(key) = _)
          }
      }

    def recursive[A, B](f: Parser[A, B] => Parser[A, B]): Parser[A, B] = {
      val id     = new Object()
      val bottom = Failure(Exception("recursion bottom")): Try[(result: B, state: ParserState)]

      def improved(
        current: Try[(result: B, state: ParserState)],
        next: Try[(result: B, state: ParserState)],
      ): Boolean = {
        (current, next) match {
          case (Failure(_), Failure(_))                => false
          case (Failure(_), Success(_))                => true
          case (Success(_), Failure(_))                => false
          case (Success(currentRes), Success(nextRes)) =>
            nextRes.state.tokens.length <= currentRes.state.tokens.length
        }
      }

      def parser(headA: A)(head: ParserState): Try[(result: B, state: ParserState)] = {
        val key = (id, headA, head.tokens)
        head.memo.get(key) match {
          case Some(cached) =>
            cached.asInstanceOf[Try[(result: B, state: ParserState)]]
          case None =>
            val mark          = head.memo.size
            var current       = bottom
            var leftRecursive = false

            def restore(): Unit = {
              while head.memo.size > mark do {
                val _ = head.memo.remove(head.memo.last._1)
              }
            }

            val self: Parser[A, B] = {
              a => s =>
                if s.tokens == head.tokens && a == headA then {
                  leftRecursive = true
                  current
                } else parser(a)(s)
            }

            @annotation.tailrec
            def iterate(step: Int): Try[(result: B, state: ParserState)] = {
              step match {
                case 0 => current
                case n =>
                  restore()
                  head.memo(key) = current
                  val next = f(self)(headA)(head)
                  if !improved(current, next) then current
                  else {
                    current = next
                    iterate(n - 1)
                  }
              }
            }

            def grow(length: Int): Try[(result: B, state: ParserState)] = {
              iterate(length).tap(_ => restore())
            }

            head.memo(key) = bottom
            val first  = f(self)(headA)(head)
            val result =
              if !leftRecursive then first
              else {
                current = first
                grow(head.tokens.length)
              }

            head.memo(key) = result
            result
        }
      }

      parser
    }
  }
}
