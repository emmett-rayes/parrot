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
}
