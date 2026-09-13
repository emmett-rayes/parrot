package parrot

/** An algebra of parsers. */
trait ParserAlgebra {
  type Self[_, _]
  type P = Self

  /** A parser that consumes a literal at the start of the input. */
  def literal(expected: String): P[Unit, expected.type]

  /** A parser that always succeeds with the given result. */
  def success[A, B](result: B): P[A, B]

}

object ParserAlgebra {

  /** Summons the parser algebra of *P*. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = {
    summon
  }
}
