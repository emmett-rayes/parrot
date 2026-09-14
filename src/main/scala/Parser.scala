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
  given ParserIsParserAlgebra: Parser is ParserAlgebra {
    import scala.util.{Failure, Success}

    given P: Parser is Profunctor = summon
    export P.dimap

    def literal(expected: String): Parser[Unit, expected.type] = {
      _ => input =>
        {
          if input.startsWith(expected)
          then Success((expected, input.drop(expected.length)))
          else Failure(Exception(s"expected $expected at this position"))
        }
    }

    def success[A, B](result: B): Parser[A, B] = {
      Promonad[Parser].unit(_ => result)
    }

    def failure[A, B]: Parser[A, B] = {
      PromonoidPlus[Parser].zero
    }

    extension [A, B](self: Parser[A, B])
      def lookahead: Parser[A, Unit] = {
        given Parser is RestrictionPromonad = summon // to assist type inference
        self.restrict.rmap(_ => ())
      }

    extension [A, B](self: Parser[A, B])
      def andThen[C](other: Parser[B, C]): Parser[A, C] = {
        self.combine(other)
      }

    extension [A, B](self: Parser[A, B])
      def orElse(other: Parser[A, B]): Parser[A, B] = {
        self.plus(other)
      }

    extension [A, B](self: Parser[A, B])
      def zip[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
        given Parser is CartesianMonoidalProfunctor = summon // to assist type inference
        self.tensor(other)
      }

    extension [A, B](self: Parser[A, B])
      def branch[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = {
        given Parser is CoMonoidalProfunctor = summon // to assist type inference
        self.sum(other)
      }
  }
}
