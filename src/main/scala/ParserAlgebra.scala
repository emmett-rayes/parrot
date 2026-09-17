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
    /** A parser that tries `self`, falling back to `other` on the original input if `self` fails, yielding a union of
      * results.
      */
    def union[C](other: P[A, C]): P[A, B | C] = {
      self.rmap(b => (b: B | C)) +> other.rmap(c => (c: B | C))
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
    /** A parser that sequences `self` with `other`, keeping only the result of `self`. */
    def thenSkip[C](other: P[A, C]): P[A, B] = {
      (self ** other).dimap(a => (a, a), (b, _) => b)
    }

  extension [A, B](self: P[A, B])
    /** A parser that sequences `self` with `other`, pairing both results. */
    def pair[C](other: P[A, C]): P[A, (B, C)] = {
      (self ** other).lmap(a => (a, a))
    }

  extension [A, B](self: P[A, B])
    /** A parser that sequences `first`, `self`, and `second`, keeping only the result of `self`. */
    def between[C, D](first: P[A, C], second: P[A, D]): P[A, B] = {
      first *> self >* second
    }

  extension [A, B](self: P[A, B])
    /** A parser that executes `self` exactly `n` times, collecting the results into a list. */
    def times(n: Int): P[A, List[B]] = {
      require(n >= 0, "n must be non-negative")
      val split: P[(A, Int, List[B]), Either[List[B], (A, Int, List[B])]] = pure {
        case (a, k, bs) =>
          if k <= 0 then Left(bs.reverse)
          else Right((a, k, bs))
      }
      val state = pure(identity[A]) ** self ** pure(identity[(Int, List[B])])
      val continue: P[(A, Int, List[B]), (A, Int, List[B])] = state.dimap(
        { case (a, k, bs) => ((a, a), (k, bs)) },
        { case ((a, b), (k, bs)) => (a, k - 1, b :: bs) }
      )

      val break = pure(identity[List[B]])
      val step  = split >> (break ++ continue)
      step.loop.lmap(a => (a, n, List.empty))
    }

  extension [A, B](self: P[A, B])
    /** A parser that executes `self` at least `n` times, collecting the results into a list. */
    def atLeast(n: Int): P[A, List[B]] = {
      require(n >= 0, "n must be non-negative")
      (self.times(n) && self.repeated).rmap((bs1, bs2) => bs1 ++ bs2)
    }

  extension [A, B](self: P[A, B])
    /** A parser that applies `self` one or more times separated by `separator`, collecting the results into a list. */
    def separatedBy[C](separator: P[A, C]): P[A, List[B]] = {
      (self ** (separator *> self).repeated).dimap(a => (a, a), { case (head, tail) => head :: tail })
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
    /** Alias for [[pair]] */
    def &&[C](other: P[A, C]): P[A, (B, C)] = {
      (self ** other).lmap(a => (a, a))
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

  extension [A, B](self: P[A, B])
    /** Alias for [[thenSkip]]. */
    def >*[C](other: P[A, C]): P[A, B] = {
      self.thenSkip(other)
    }
}

object ParserAlgebra {

  /** Summons the `ParserAlgebra` instance of `P`. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = {
    summon
  }
}
