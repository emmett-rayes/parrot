package parrot

/** An algebra of parsers. */
trait ParserAlgebra {
  type Self[_, _]: Profunctor
  type P = Self

  /** A parser that consumes a literal at the start of the input. */
  def literal(expected: String): P[Unit, String]

  /** A parser that consumes a regular expression match at the start of the input. */
  def regex(expected: scala.util.matching.Regex): P[Unit, String]

  /** A parser that succeeds without consuming input, computing its result by applying `f` to the semantic input. */
  def pure[A, B](f: A => B): P[A, B]

  /** A parser defined recursively by computing the fixed point of `f`. */
  def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B]

  /** A tuple of parsers defined mutually recursively by computing the simultaneous fixed point of tuple of parsers via
    * Bekic's theorem.
    */
  inline def recursive[T <: Tuple](f: T => T): T = {
    inline compiletime.erasedValue[T] match {
      case _: EmptyTuple => {
        EmptyTuple.asInstanceOf[T]
      }
      case _: (head *: tail) => {
        def solveHead(t: tail): head = {
          recursive[Any, Any](h =>
            f((h.asInstanceOf[head] *: t).asInstanceOf[T]).productElement(0).asInstanceOf[P[Any, Any]]
          ).asInstanceOf[head]
        }

        val solvedTail = recursive[tail](t => f((solveHead(t) *: t).asInstanceOf[T]).drop(1).asInstanceOf[tail])
        val solvedHead = solveHead(solvedTail)

        (solvedHead *: solvedTail).asInstanceOf[T]
      }
    }
  }

  /** A parser that always succeeds with the given result. */
  def success[A, B](result: B): P[A, B] = {
    pure(_ => result)
  }

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

  extension [A, B](self: P[A, Either[B, A]])
    /** A parser that repeatedly executes `self` while it yields `Right`, and terminates when it yields `Left`. */
    def loop: P[A, B]

  extension [A, B](self: P[A, B])
    /** A parser that repeatedly executes `self` until it fails, collecting the results into a list. */
    def repeated: P[A, List[B]] = {
      val break: P[(A, List[B]), List[B]]                = pure(_._2.reverse)
      val state: P[((A, A), List[B]), ((A, B), List[B])] = pure(identity[A]) ** self ** pure(identity[List[B]])
      val continue: P[(A, List[B]), (A, List[B])]        = state.dimap(
        { case (a, bs) => ((a, a), bs) },
        { case ((a, b), bs) => (a, b :: bs) }
      )
      val step = (continue |> break).rmap(_.swap)
      step.loop.lmap((_: A, List.empty))
    }

  extension [A, B](self: P[A, B])
    /** A parser that tries `self`, returning `Some` on success or `None` on failure. */
    def optional: P[A, Option[B]] = {
      self.rmap(Some(_)) +> success(None)
    }

  extension [A, B](self: P[A, B])
    /** A parser that sequences `self` with `other`, keeping only the result of `other`. */
    def skipThen[C](other: P[A, C]): P[A, C] = {
      (self ** other).dimap(a => (a, a), (_, c) => c)
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

  extension [A, B](self: P[A, B])
    /** Alias for [[skipThen]]. */
    def *>[C](other: P[A, C]): P[A, C] = {
      self.skipThen(other)
    }
}

object ParserAlgebra {

  /** Summons the `ParserAlgebra` instance of `P`. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = {
    summon
  }
}
