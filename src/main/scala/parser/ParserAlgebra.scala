package parrot
package parser

import category.*

import scala.annotation.targetName
import scala.util.matching.Regex

/** An algebra of parsers.
  *
  * A parser `P[A, B]` consumes a prefix of the input while turning a semantic input `A` into a *semantic result `B`.
  */
trait ParserAlgebra {
  type Self[_, _]
  final type P = Self

  /** Pure functions on semantic values. */
  type On[_, _]
  final type ==> = On

  /** The empty semantic value. */
  type Empty

  /** Pairs of semantic values. */
  type Pair[_, _]
  final type * = Pair

  /** The impossible semantic value. */
  type None

  /** Tagged alternatives of semantic values: `A + B` is either an `A` or a `B`. */
  type Alternative[_, _]
  final type + = Alternative

  /** Collections of semantic values. */
  type Many[_]

  /** Names `self` as the rule `label`, for diagnostics, memoization, tracing etc. */
  def rule[A, B](self: P[A, B], label: String): P[A, B]

  /** Consumes `expected`. */
  def literal(expected: String): P[Empty, String]

  /** Consumes a match of `expected`. */
  def regex(expected: Regex): P[Empty, String]

  /** Applies `f` to the semantic input without consuming anything. */
  def pure[A, B](f: A ==> B): P[A, B]

  /** Applies `g` to the result of `self`. */
  def map[A, B, D](self: P[A, B], g: B ==> D): P[A, D]

  /** Applies `f` to the semantic input before passing it to `self`. */
  def mapInput[A, B, C](self: P[A, B], f: C ==> A): P[C, B]

  /** Succeeds without consuming anything, returning its semantic input. */
  def success[A]: P[A, A]

  /** Runs `self`, then `other` on the remaining input with the result of `self` as its semantic input. */
  def andThen[A, B, C](self: P[A, B], other: P[B, C]): P[A, C]

  /** Runs `self` on the left of a pair of semantic inputs, then `other` on the right, pairing their results. */
  def zip[A, B, C, D](self: P[A, B], other: P[C, D]): P[A * C, B * D]

  /** Runs `self`, then `other`, on the same semantic input, pairing their results. */
  def pair[A, B, C](self: P[A, B], other: P[A, C]): P[A, B * C]

  /** Runs `self`, then `other`, keeping only the result of `other`. */
  def skipThen[A, B, C](self: P[A, B], other: P[A, C]): P[A, C]

  /** Runs `self`, then `other`, keeping only the result of `self`. */
  def thenSkip[A, B, C](self: P[A, B], other: P[A, C]): P[A, B]

  /** Runs `open`, `self`, then `close`, keeping the result of `self`. */
  def between[A, B, C, D](self: P[A, B], open: P[A, C], close: P[A, D]): P[A, B]

  /** Runs `self` on a left semantic input or `other` on a right one, tagging the result accordingly. */
  def branch[A, B, C, D](self: P[A, B], other: P[C, D]): P[A + C, B + D]

  /** Runs `self` on a left semantic input or `other` on a right one, into a common result. */
  def merge[A, B, C](self: P[A, B], other: P[C, B]): P[A + C, B]

  /** Always fails without consuming anything. */
  def failure[A, B]: P[A, B]

  /** Tries `self` and, only if it fails, `other` on the original input. */
  def orElse[A, B](self: P[A, B], other: P[A, B]): P[A, B]

  /** Tries `self` and, only if it fails, `other` on the original input, tagging the alternative that succeeded. */
  def or[A, B, C](self: P[A, B], other: P[A, C]): P[A, B + C]

  /** Tries `self`; if it fails, succeeds without consuming anything, returning the semantic input on the right. */
  def optional[A, B](self: P[A, B]): P[A, B + A] = {
    self +> success
  }

  /** Succeeds if and only if `self` succeeds, consuming nothing and returning the semantic input. */
  def lookahead[A, B](self: P[A, B]): P[A, A]

  /** Succeeds if and only if `self` fails, consuming nothing and returning the semantic input.
    */
  def not[A, B](self: P[A, B]): P[A, A] = {
    (~self +> success) >> (failure || success)
  }

  /** Runs `self` repeatedly, feeding each right result back as the next semantic input, until it yields a left result.
    */
  def iterate[A, B](self: P[A, B + A]): P[A, B]

  /** Runs `self` zero or more times until it fails, collecting the results. */
  def repeated[A, B](self: P[A, B]): P[A, Many[B]]

  /** Runs `self` exactly `n` times, collecting the results. */
  def times[A, B](self: P[A, B], n: Int): P[A, Many[B]]

  /** Runs `self` at least `n` times until it fails, collecting the results. */
  def atLeast[A, B](self: P[A, B], n: Int): P[A, Many[B]]

  /** Runs `self` one or more times separated by `separator`, collecting the results. */
  def separatedBy[A, B, C](self: P[A, B], separator: P[A, C]): P[A, Many[B]]

  /** The parser defined recursively by `f`, which receives the parser being defined. */
  def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B]

  /** A tuple of mutually recursive parsers, solved one parser at a time via Bekić's theorem.
    *
    * fix(*x*, *y*) = (fix *x* . *f₁*(*x*, *y₀*), *y₀*) where *y₀* = fix *y* . *f₂*(fix *x*. *f₁*(*x*, *y*), *y*).
    */
  inline def recursive[T <: Tuple](f: T => T): T = {
    inline compiletime.erasedValue[T] match {
      case _: EmptyTuple     => EmptyTuple.asInstanceOf[T]
      case _: (head *: tail) =>
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

  extension [A, B](self: P[A, B])
    /** Infix extension for [[rule]]. */
    @targetName("ruleExt")
    def rule(label: String): P[A, B] = {
      ParserAlgebra.this.rule(self, label)
    }

    /** Infix extension for [[map]]. */
    @targetName("mapExt")
    def map[D](g: B ==> D): P[A, D] = {
      ParserAlgebra.this.map(self, g)
    }

    /** Infix extension for [[mapInput]]. */
    @targetName("mapInputExt")
    def mapInput[C](f: C ==> A): P[C, B] = {
      ParserAlgebra.this.mapInput(self, f)
    }

    /** Infix extension for [[andThen]]. */
    @targetName("andThenExt")
    def andThen[C](other: P[B, C]): P[A, C] = {
      ParserAlgebra.this.andThen(self, other)
    }

    /** Infix extension for [[zip]]. */
    @targetName("zipExt")
    def zip[C, D](other: P[C, D]): P[A * C, B * D] = {
      ParserAlgebra.this.zip(self, other)
    }

    /** Infix extension for [[pair]]. */
    @targetName("pairExt")
    def pair[C](other: P[A, C]): P[A, B * C] = {
      ParserAlgebra.this.pair(self, other)
    }

    /** Infix extension for [[skipThen]]. */
    @targetName("skipThenExt")
    def skipThen[C](other: P[A, C]): P[A, C] = {
      ParserAlgebra.this.skipThen(self, other)
    }

    /** Infix extension for [[thenSkip]]. */
    @targetName("thenSkipExt")
    def thenSkip[C](other: P[A, C]): P[A, B] = {
      ParserAlgebra.this.thenSkip(self, other)
    }

    /** Infix extension for [[between]]. */
    @targetName("betweenExt")
    def between[C, D](open: P[A, C], close: P[A, D]): P[A, B] = {
      ParserAlgebra.this.between(self, open, close)
    }

    /** Infix extension for [[branch]]. */
    @targetName("branchExt")
    def branch[C, D](other: P[C, D]): P[A + C, B + D] = {
      ParserAlgebra.this.branch(self, other)
    }

    /** Infix extension for [[merge]]. */
    @targetName("mergeExt")
    def merge[C](other: P[C, B]): P[A + C, B] = {
      ParserAlgebra.this.merge(self, other)
    }

    /** Infix extension for [[orElse]]. */
    @targetName("orElseExt")
    def orElse(other: P[A, B]): P[A, B] = {
      ParserAlgebra.this.orElse(self, other)
    }

    /** Infix extension for [[or]]. */
    @targetName("orExt")
    def or[C](other: P[A, C]): P[A, B + C] = {
      ParserAlgebra.this.or(self, other)
    }

    /** Infix extension for [[optional]]. */
    @targetName("optionalExt")
    def optional(using DummyImplicit): P[A, B + A] = {
      ParserAlgebra.this.optional(self)
    }

    /** Infix extension for [[lookahead]]. */
    @targetName("lookaheadExt")
    def lookahead(using DummyImplicit): P[A, A] = {
      ParserAlgebra.this.lookahead(self)
    }

    /** Infix extension for [[not]]. */
    @targetName("notExt")
    def not(using DummyImplicit): P[A, A] = {
      ParserAlgebra.this.not(self)
    }

    /** Infix extension for [[repeated]]. */
    @targetName("repeatedExt")
    def repeated(using DummyImplicit): P[A, Many[B]] = {
      ParserAlgebra.this.repeated(self)
    }

    /** Infix extension for [[times]]. */
    @targetName("timesExt")
    def times(n: Int): P[A, Many[B]] = {
      ParserAlgebra.this.times(self, n)
    }

    /** Infix extension for [[atLeast]]. */
    @targetName("atLeastExt")
    def atLeast(n: Int): P[A, Many[B]] = {
      ParserAlgebra.this.atLeast(self, n)
    }

    /** Infix extension for [[separatedBy]]. */
    @targetName("separatedByExt")
    def separatedBy[C](separator: P[A, C]): P[A, Many[B]] = {
      ParserAlgebra.this.separatedBy(self, separator)
    }

  extension [A, B](self: P[A, B + A])
    /** Infix extension for [[iterate]]. */
    @targetName("loopExt")
    def iterate(using DummyImplicit): P[A, B] = {
      ParserAlgebra.this.iterate(self)
    }

  extension [A, B](self: P[A, B])
    /** Alias for [[andThen]]. */
    def >>[C](other: P[B, C]): P[A, C] = self.andThen(other)

    /** Alias for [[zip]]. */
    def **[C, D](other: P[C, D]): P[A * C, B * D] = self.zip(other)

    /** Alias for [[pair]]. */
    def &&[C](other: P[A, C]): P[A, B * C] = self.pair(other)

    /** Alias for [[skipThen]]. */
    def *>[C](other: P[A, C]): P[A, C] = self.skipThen(other)

    /** Alias for [[thenSkip]]. */
    def <*[C](other: P[A, C]): P[A, B] = self.thenSkip(other)

    /** Alias for [[branch]]. */
    def ++[C, D](other: P[C, D]): P[A + C, B + D] = self.branch(other)

    /** Alias for [[merge]]. */
    def ||[C](other: P[C, B]): P[A + C, B] = self.merge(other)

    /** Alias for [[orElse]]. */
    def |>(other: P[A, B]): P[A, B] = self.orElse(other)

    /** Alias for [[or]]. */
    def +>[C](other: P[A, C]): P[A, B + C] = self.or(other)

    /** Alias for [[lookahead]]. */
    def unary_~ : P[A, A] = self.lookahead

    /** Alias for [[not]]. */
    def unary_! : P[A, A] = self.not

  /** Equations between deterministic, backtracking (PEG-style) parsers. */
  object ParserLaws {

    /** Running `success` first changes nothing. */
    def leftIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (success >> p) === p
    }

    /** Running `success` last changes nothing. */
    def rightIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (p >> success) === p
    }

    /** Sequencing is associative. */
    def associativity[A, B, C, D](p: P[A, B], q: P[B, C], r: P[C, D])(using P[A, D] is Eq): Boolean = {
      ((p >> q) >> r) === (p >> (q >> r))
    }

    /** Zipping two `success` parsers is `success` on pairs. */
    def zipIdentity[A, C](using P[A * C, A * C] is Eq): Boolean = {
      (success ** success) === success
    }

    /** Nothing runs after a failure. */
    def leftZero[A, B, C](p: P[B, C])(using P[A, C] is Eq): Boolean = {
      (failure >> p) === failure
    }

    /** A failure at the end fails the whole sequence. */
    def rightZero[A, B, C](p: P[A, B])(using P[A, C] is Eq): Boolean = {
      (p >> failure) === failure
    }

    /** A failing first alternative is skipped. */
    def choiceLeftIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (failure |> p) === p
    }

    /** A failing last alternative is never needed. */
    def choiceRightIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (p |> failure) === p
    }

    /** Ordered choice is associative. */
    def choiceAssociativity[A, B](p: P[A, B], q: P[A, B], r: P[A, B])(using P[A, B] is Eq): Boolean = {
      ((p |> q) |> r) === (p |> (q |> r))
    }

    /** Checking that `p` would succeed before running it changes nothing. */
    def lookaheadIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (~p >> p) === p
    }

    /** Lookaheads commute. */
    def lookaheadCommutativity[A, B, C](p: P[A, B], q: P[A, C])(using P[A, A] is Eq): Boolean = {
      (~p >> ~q) === (~q >> ~p)
    }

    /** Looking ahead at a guarded parser is looking ahead at the guard and the parser. */
    def lookaheadCompose[A, B, C](p: P[A, B], q: P[A, C])(using P[A, A] is Eq): Boolean = {
      ~(~p >> q) === (~p >> ~q)
    }

    /** Looking ahead after `p` is looking ahead at `p` followed by its continuation, then running `p`. */
    def lookaheadPrecompose[A, B, C](p: P[A, B], q: P[B, C])(using P[A, B] is Eq): Boolean = {
      (p >> ~q) === (~(p >> q) >> p)
    }

    /** A double negative lookahead is a positive lookahead. */
    def doubleNegation[A, B](p: P[A, B])(using P[A, A] is Eq): Boolean = {
      !(!p) === ~p
    }

    /** A parser cannot both succeed and fail. */
    def negationExclusion[A, B](p: P[A, B])(using P[A, A] is Eq): Boolean = {
      (~p >> !p) === failure
    }

    /** A recursive parser is its own unfolding. */
    def recursionUnfolding[A, B](f: P[A, B] => P[A, B])(using P[A, B] is Eq): Boolean = {
      recursive(f) === f(recursive(f))
    }

    /** A loop is one step followed by either stopping or looping again. */
    def loopUnfolding[A, B](p: P[A, B + A])(using P[A, B] is Eq): Boolean = {
      p.iterate === (p >> (success || p.iterate))
    }
  }
}

/** Utilities and mixins for [[ParserAlgebra]]. */
object ParserAlgebra {

  /** A [[ParserAlgebra]] equipped with all the categorical mixins. */
  trait CanonicalParser
      extends ParserAlgebra,
        Sequencing,
        Zipping,
        Branching,
        Alternation,
        Lookahead,
        Repetition,
        Recursion,
        Pairing,
        Iteration {
    override val OnIsCartesian: On is Cartesian.`with`[Empty, Pair] = RepetitionOnCartesian
  }

  /** An algebra whose semantic values are the standard Scala ones: `Unit`, `Tuple2`, `Either`, `Nothing` and `Vector`.
    */
  type Standard = ParserAlgebra {
    type Empty       = Unit
    type Pair        = Tuple2
    type None        = Nothing
    type Alternative = Either
    type Many        = Vector
  }

  /** Summons the `ParserAlgebra` instance of `P`. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = summon
}
