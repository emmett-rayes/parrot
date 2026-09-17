package parrot

import scala.util.Try

/** A Parser over `String` input with `Throwable` failures.
  *
  * A parser of type *P*[*A*,*B*] maps an input *A* and a `String` to either a failure or a result *B* paired with the
  * unconsumed remainder of the `String`.
  *
  * Implemented as the Kleisli profunctor of the state monad over the `Try` monad, where
  *   - *P*[*A*,*B*] = *A* → `String` → ((*B* × `String`) + `Throwable`) is the object part
  *   - *P*(*f*,*g*) = *f* ; - ; ((*g* × *id*) + *id*) is the morphism part
  */
type Parser = Kleisli[StateT[String, Try]]

object Parser {
  import Kleisli.given
  import Promonad.given
  import StateT.given

  extension [A, B](self: Parser[A, B])
    /** Runs a parser on a given state and semantic input. */
    def run(a: A, input: String): Try[(result: B, state: String)] = {
      self(a)(input)
    }

  extension [B](self: Parser[Unit, B])
    /** Runs a parser on a given state. */
    def run(input: String): Try[(result: B, state: String)] = {
      self(())(input)
    }

  /** The canonical parser implementation is a parser algebra. */
  given ParserIsCanonicalParser: Parser is CanonicalParser {
    import scala.util.{Failure, Success}

    def literal(expected: String): Parser[Unit, expected.type] = {
      _ => input =>
        {
          if input.startsWith(expected)
          then Success((expected, input.drop(expected.length)))
          else Failure(Exception(s"expected $expected at this position"))
        }
    }

    def recursive[A, B](f: Parser[A, B] => Parser[A, B]): Parser[A, B] = {
      val bottom: Try[(result: B, state: String)] = Failure(Exception("recursion bottom"))

      def improved(current: Try[(result: B, state: String)], next: Try[(result: B, state: String)]): Boolean = {
        (current, next) match {
          case (Failure(_), Failure(_))                    => false
          case (Failure(_), Success(_))                    => true
          case (Success(_), Failure(_))                    => false
          case (Success((_, current)), Success((_, next))) => next.length < current.length
        }
      }

      headA =>
        headInput => {
          var current       = bottom
          var leftRecursive = false

          val self: Parser[A, B] = {
            a => input =>
              {
                if input == headInput then {
                  leftRecursive = true
                  current
                } else {
                  recursive(f)(a)(input)
                }
              }
          }

          @annotation.tailrec
          def iterate(step: Int): Try[(result: B, state: String)] = {
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
