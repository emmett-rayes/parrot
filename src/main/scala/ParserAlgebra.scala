package parrot

/** An algebra of parsers. */
trait ParserAlgebra {
  type Self[_, _]
  type P = Self

  /** A parser that consumes a literal at the start of the input. */
  def literal(expected: String): P[Unit, expected.type]

  /** A parser that always succeeds with the given result. */
  def success[A, B](result: B): P[A, B]

  /** A parser that always fails. */
  def failure[A, B]: P[A, B]

  extension [A, B](self: P[A, B])
    /** A parser that sequences `self` with `other`, passing the result of `self` as input to `other` on the remaining
      * input.
      */
    def andThen[C](other: P[B, C]): P[A, C]

  extension [A, B](self: P[A, B])
    /** A parser that sequences `self` with `other`, pairing their respective inputs and results while passing the
      * remaining input to `other`.
      */
    def zip[C, D](other: P[C, D]): P[(A, C), (B, D)]

  extension [A, B](self: P[A, B])
    /** Alias for [[zip]]. */
    def **[C, D](other: P[C, D]): P[(A, C), (B, D)] = {
      self.zip(other)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[andThen]]. */
    def >>[C](other: P[B, C]): P[A, C] = {
      self.andThen(other)
    }
}

object ParserAlgebra {

  /** Summons the parser algebra of *P*. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = {
    summon
  }
}
