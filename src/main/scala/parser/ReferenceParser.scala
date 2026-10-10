package parrot
package parser

import parrot.category.{Cartesian, Cocartesian}

import scala.util.matching.Regex

/** The reference interpreter of [[ParserAlgebra]]: the specification against which other interpreters are checked.
  *
  * It interprets the algebra on the standard structure of **Type** (`Function`, `Tuple2`/`Unit`, `Either`/`Nothing`,
  * `Vector`) and implements only the primitives; every derived combinator comes from the generic mixins, so testing
  * this interpreter also tests the derivations.
  *
  * Parsers are ordered-choice (PEG) parsers with full backtracking. Fixed points are naive unfoldings, so
  * left-recursive grammars diverge, as do iterations of parsers that succeed without consuming input.
  */
object ReferenceParser
    extends ParserAlgebra,
      ParserAlgebra.Mapping,
      ParserAlgebra.Zipping,
      ParserAlgebra.Pairing,
      ParserAlgebra.AlternativeBranching,
      ParserAlgebra.Optional,
      ParserAlgebra.Negation,
      ParserAlgebra.Iteration {

  /** The outcome of running a parser. */
  enum Result[+B] derives CanEqual {

    /** Success with a semantic `value` after consuming the input up to `offset`. */
    case Success(value: B, offset: Int)

    /** Failure at `offset`, expecting `expected`. */
    case Failure(offset: Int, expected: String) extends Result[Nothing]
  }

  /** A parser maps a semantic input and a position in `source` to a [[Result]]. */
  trait Parser[-A, +B] {
    def apply(a: A, source: String, offset: Int): Result[B]
  }

  import Result.{Failure, Success}

  type Self[A, B]      = Parser[A, B]
  type On[A, B]        = Function[A, B]
  type I               = Unit
  type Tensor[A, B]    = (A, B)
  type Z               = Nothing
  type Coproduct[A, B] = Either[A, B]
  type Many[B]         = Vector[B]

  override val OnIsCartesian: Cartesian.FunctionIsCartesian.type     = Cartesian.FunctionIsCartesian
  override val OnIsCocartesian: Cocartesian.FunctionIsCocartesian.type = Cocartesian.FunctionIsCocartesian

  override def nil[B]: Unit => Vector[B] = _ => Vector.empty

  override def snoc[B]: ((Vector[B], B)) => Vector[B] = (bs, b) => bs :+ b

  /** Of two failures, keeps the one that got furthest into the input. */
  private def furthest(x: Failure, y: Failure): Failure = if y.offset > x.offset then y else x

  extension [B](self: P[Unit, B])
    /** Runs `self` on a prefix of `source`. */
    def parse(source: String): Result[B] = self((), source, 0)

    /** Runs `self` on the whole of `source`. */
    def parseAll(source: String): Result[B] = self.thenSkip(regex("(?s).".r).not).parse(source)

  // ===========================================================================
  // Primitives
  // ===========================================================================

  extension [A, B](self: P[A, B])
    override def rule(label: String): P[A, B] = { (a, source, offset) =>
      self(a, source, offset) match {
        case Failure(at, _) if at == offset => Failure(at, label)
        case result                         => result
      }
    }

  override def literal(expected: String): P[Unit, String] = { (_, source, offset) =>
    if source.startsWith(expected, offset) then Success(expected, offset + expected.length)
    else Failure(offset, s"\"$expected\"")
  }

  override def regex(expected: Regex): P[Unit, String] = { (_, source, offset) =>
    val matcher = expected.pattern.matcher(source).region(offset, source.length)
    if matcher.lookingAt() then Success(matcher.group(), matcher.end())
    else Failure(offset, s"/${expected.regex}/")
  }

  override def pure[A, B](f: A => B): P[A, B] = { (a, _, offset) =>
    Success(f(a), offset)
  }

  override def success[A]: P[A, A] = { (a, _, offset) =>
    Success(a, offset)
  }

  override def failure[A, B]: P[A, B] = { (_, _, offset) =>
    Failure(offset, "failure")
  }

  extension [A, B](self: P[A, B])
    override def andThen[C](other: P[B, C]): P[A, C] = { (a, source, offset) =>
      self(a, source, offset) match {
        case Success(b, next) => other(b, source, next)
        case f: Failure       => f
      }
    }

    override def zip[C, D](other: P[C, D]): P[(A, C), (B, D)] = { (ac, source, offset) =>
      self(ac._1, source, offset) match {
        case Success(b, next) =>
          other(ac._2, source, next) match {
            case Success(d, last) => Success((b, d), last)
            case f: Failure       => f
          }
        case f: Failure => f
      }
    }

    override def branch[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = { (ac, source, offset) =>
      ac match {
        case Left(a) =>
          self(a, source, offset) match {
            case Success(b, next) => Success(Left(b), next)
            case f: Failure       => f
          }
        case Right(c) =>
          other(c, source, offset) match {
            case Success(d, next) => Success(Right(d), next)
            case f: Failure       => f
          }
      }
    }

    override def orElse(other: P[A, B]): P[A, B] = { (a, source, offset) =>
      self(a, source, offset) match {
        case success: Success[B] => success
        case f: Failure          =>
          other(a, source, offset) match {
            case success: Success[B] => success
            case g: Failure          => furthest(f, g)
          }
      }
    }

    override def lookahead: P[A, A] = { (a, source, offset) =>
      self(a, source, offset) match {
        case Success(_, _) => Success(a, offset)
        case f: Failure    => f
      }
    }

  extension [A, B](self: P[A, Either[B, A]])
    override def loop: P[A, B] = { (a, source, offset) =>
      @annotation.tailrec
      def go(a: A, offset: Int): Result[B] = self(a, source, offset) match {
        case Success(Left(b), next)  => Success(b, next)
        case Success(Right(a), next) => go(a, next)
        case f: Failure              => f
      }
      go(a, offset)
    }

  override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = {
    lazy val fixed: P[A, B] = f((a, source, offset) => fixed(a, source, offset))
    fixed
  }
}
