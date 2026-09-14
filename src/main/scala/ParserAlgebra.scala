package parrot

/** An algebra of parsers. */
trait ParserAlgebra {
  type Self[_, _]: Profunctor
  type P = Self

  /** A parser that consumes a literal at the start of the input. */
  def literal(expected: String): P[Unit, expected.type]

  /** A parser that always succeeds with the given result. */
  def success[A, B](result: B): P[A, B]

  /** A parser that always fails. */
  def failure[A, B]: P[A, B]

  extension [A, B](self: P[A, B])
    /** A parser that succeeds if `self` succeeds but without consuming any input. */
    def lookahead: P[A, Unit]

  extension [A, B](self: P[A, B])
    /** A parser that succeeds if `self` fails, and fails if `self` succeeds. */
    def not: P[A, Unit] = {
      self.lookahead
        .either(success(()))
        .andThen(failure.merge(success(())))
    }

  extension [A, B](self: P[A, B])
    /** A parser that sequences `self` with `other`, passing the result of `self` as input to `other` on the remaining
      * input.
      */
    def andThen[C](other: P[B, C]): P[A, C]

  extension [A, B](self: P[A, B])
    /** A parser that tries `self`, falling back to `other` on the original input if `self` fails, yielding a common
      * result.
      */
    def orElse(other: P[A, B]): P[A, B]

  extension [A, B](self: P[A, B])
    /** A parser that tries `self`, falling back to `other` on the original input if `self` fails. */
    def either[C](other: P[A, C]): P[A, Either[B, C]] = {
      self.rmap(Left(_)).orElse(other.rmap(Right(_)))
    }

  extension [A, B](self: P[A, B])
    /** A parser that sequences `self` with `other`, pairing their respective inputs and results while passing the
      * remaining input to `other`.
      */
    def zip[C, D](other: P[C, D]): P[(A, C), (B, D)]

  extension [A, B](self: P[A, B])
    /** A parser that dispatches between `self` and `other` based on the input. */
    def branch[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]]

  extension [A, B](self: P[A, B])
    /** A parser that dispatches between `self` and `other` based on the input, merging to a common result. */
    def merge[C](other: P[C, B]): P[Either[A, C], B] = {
      self.branch(other).rmap(_.merge)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[lookahead]]. */
    def unary_~ : P[A, Unit] = {
      self.lookahead
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[not]]. */
    def unary_! : P[A, Unit] = {
      self.not
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[andThen]]. */
    def >>[C](other: P[B, C]): P[A, C] = {
      self.andThen(other)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[orElse]]. */
    def +>(other: P[A, B]): P[A, B] = {
      self.orElse(other)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[either]]. */
    def |>[C](other: P[A, C]): P[A, Either[B, C]] = {
      self.either(other)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[zip]]. */
    def **[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
      self.zip(other)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[branch]]. */
    def ++[C, D](other: P[C, D]): P[Either[A, C], Either[B, D]] = {
      self.branch(other)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[merge]]. */
    def ||[C](other: P[C, B]): P[Either[A, C], B] = {
      self.merge(other)
    }
}

object ParserAlgebra {

  /** Summons the `ParserAlgebra` instance of `P`. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = {
    summon
  }
}
