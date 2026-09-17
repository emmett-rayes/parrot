package parrot

import scala.util.Try

/** A Parser over `Tokens` input with `Throwable` failures.
  *
  * A parser of type *P*[*A*,*B*] maps an input *A* and a `Tokens` to either a failure or a result *B* paired with the
  * unconsumed remainder of the `Tokens`.
  *
  * Implemented as the Kleisli profunctor of the state monad over the `Try` monad, where
  *   - *P*[*A*,*B*] = *A* → `Tokens` → ((*B* × `Tokens`) + `Throwable`) is the object part
  *   - *P*(*f*,*g*) = *f* ; - ; ((*g* × *id*) + *id*) is the morphism part
  */
type Parser = Kleisli[StateT[Tokens, Try]]

object Parser {
  import Kleisli.given
  import Promonad.given
  import StateT.given

  extension [A, B](self: Parser[A, B])
    /** Runs a parser on a given state and semantic input. */
    def run(a: A, input: Tokens): Try[(result: B, state: Tokens)] = {
      self(a)(input)
    }

    def run(a: A, input: String): Try[(result: B, state: String)] = {
      run(a, input.asTokens).map { case (result, state) => (result, state.mkString) }
    }

  extension [B](self: Parser[Unit, B])
    /** Runs a parser on a given state. */
    def run(input: Tokens): Try[(result: B, state: Tokens)] = {
      self(())(input)
    }

    def run(input: String): Try[(result: B, state: String)] = {
      run(input.asTokens).map { case (result, state) => (result, state.mkString) }
    }

  /** The canonical parser implementation is a parser algebra. */
  given ParserIsCanonicalParser: Parser is CanonicalParser {
    import scala.util.{Failure, Success}

    def literal(expected: String): Parser[Unit, String] = {
      val tokens = expected.asTokens
      _ => { input =>
        {
          if input.startsWith(tokens) then Success(expected, input.drop(tokens.length))
          else Failure(ParserError(s"expected $expected at this position: \"${input.context()}\"."))
        }
      }
    }

    def regex(expected: scala.util.matching.Regex): Parser[Unit, String] = {
      _ => input =>
        {
          expected.findPrefixMatchOf(input.asCharSequence) match {
            case Some(m) => Success(input.slice(m.start, m.end).mkString, input.drop(m.end))
            case None    => Failure(
                ParserError(s"no matching for ${expected.regex} at this position \"${input.context()}\".")
              )
          }
        }
    }

    def recursive[A, B](f: Parser[A, B] => Parser[A, B]): Parser[A, B] = {
      val bottom: Try[(result: B, state: Tokens)] = Failure(Exception("recursion bottom"))

      def improved(current: Try[(result: B, state: Tokens)], next: Try[(result: B, state: Tokens)]): Boolean = {
        (current, next) match {
          case (Failure(_), Failure(_))                    => false
          case (Failure(_), Success(_))                    => true
          case (Success(_), Failure(_))                    => false
          case (Success(currentRes), Success(nextRes)) =>
            nextRes.state.length <= currentRes.state.length
        }
      }

      headA => { headInput =>
        var current       = bottom
        var leftRecursive = false

        val self: Parser[A, B] = {
          a => input =>
            if input == headInput then {
              leftRecursive = true
              current
            } else recursive(f)(a)(input)
        }

        @annotation.tailrec
        def iterate(step: Int): Try[(result: B, state: Tokens)] = {
          step match {
            case 0 => current
            case n =>
              val next = f(self)(headA)(headInput)
              if !improved(current, next) then current
              else {
                current = next
                iterate(n - 1)
              }
          }
        }

        val first = f(self)(headA)(headInput)
        if !leftRecursive then first
        else {
          current = first
          iterate(headInput.length)
        }
      }
    }
  }
}
