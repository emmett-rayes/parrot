package parrot
package parser

import category.*
import category.Enriched.over
import category.Profunctor.on

import scala.util.matching.Regex

/** An algebra of parsers.
  *
  * A parser `P[A, B]` consumes a prefix of the input while turning a *semantic input* `A` into a *semantic result* `B`.
  * The algebra declares the vocabulary of parsing; it makes no assumptions about how parsers are represented or which
  * equations they satisfy. Combinators expressible with the other operations alone (`optional`, `not`) are defined
  * here; the remaining operations are implemented by the mixins in [[ParserAlgebra$ ParserAlgebra]], so that an
  * interpreter can pick, per operation, a generic implementation or a specialized one. Interpreters may override any
  * operation.
  *
  * The abstract types are
  *   - `Self` (alias `P`): parsers
  *   - `On` (alias `==>`): the pure functions that parsers can apply to semantic values without touching the input
  *   - `Pair` (alias `*`) and `Empty`: pairs of semantic values and the empty semantic value (the input of literals)
  *   - `Alternative` (alias `+`) and `None`: tagged alternatives of semantic values and the impossible value
  *   - `Many`: the collections of results produced by repetition
  */
trait ParserAlgebra {

  /** Parsers. */
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

  /** Tagged alternatives of semantic values: `A + B` is either an `A` (left) or a `B` (right). */
  type Alternative[_, _]
  final type + = Alternative

  /** Collections of results produced by repetition. */
  type Many[_]

  // ===========================================================================
  // 1. Structural / Metadata
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** Names `self` as the rule `label`, for diagnostics, memoization or tracing; does not change what it accepts. */
    def rule(label: String): P[A, B]

  // ===========================================================================
  // 2. Lexical / Primitive Matchers
  // ===========================================================================

  /** Consumes `expected` at the current position. */
  def literal(expected: String): P[Empty, String]

  /** Consumes a match of `expected` anchored at the current position. */
  def regex(expected: Regex): P[Empty, String]

  // ===========================================================================
  // 3. Embedding / Adaptation
  // ===========================================================================

  /** Applies `f` to the semantic input without consuming anything. */
  def pure[A, B](f: A ==> B): P[A, B]

  extension [A, B](self: P[A, B])
    /** Applies `g` to the result of `self`. */
    def map[D](g: B ==> D): P[A, D]

    /** Applies `f` to the semantic input before passing it to `self`. */
    def mapInput[C](f: C ==> A): P[C, B]

  // ===========================================================================
  // 4. Sequential Composition
  // ===========================================================================

  /** Succeeds without consuming anything, returning its semantic input. */
  def success[A]: P[A, A]

  extension [A, B](self: P[A, B])
    /** Runs `self`, then `other` on the remaining input with the result of `self` as its semantic input. */
    def andThen[C](other: P[B, C]): P[A, C]

  // ===========================================================================
  // 5. Parallel / Pair Composition
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** Runs `self` on the left of a pair of semantic inputs, then `other` on the right, pairing their results. */
    def zip[C, D](other: P[C, D]): P[A * C, B * D]

    /** Runs `self`, then `other`, on the same semantic input, pairing their results. */
    def pair[C](other: P[A, C]): P[A, B * C]

    /** Runs `self`, then `other`, keeping the result of `other`. */
    def skipThen[C](other: P[A, C]): P[A, C]

    /** Runs `self`, then `other`, keeping the result of `self`. */
    def thenSkip[C](other: P[A, C]): P[A, B]

    /** Runs `open`, `self`, then `close`, keeping the result of `self`. */
    def between[C, D](open: P[A, C], close: P[A, D]): P[A, B]

  // ===========================================================================
  // 6. Branching / Alternative Composition
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** Runs `self` on a left semantic input and `other` on a right one, tagging the result accordingly. */
    def branch[C, D](other: P[C, D]): P[A + C, B + D]

    /** Runs `self` on a left semantic input and `other` on a right one, into a common result. */
    def merge[C](other: P[C, B]): P[A + C, B]

  // ===========================================================================
  // 7. Alternative / Choice
  // ===========================================================================

  /** Always fails. */
  def failure[A, B]: P[A, B]

  extension [A, B](self: P[A, B])
    /** Ordered choice: tries `self` and, only if it fails, `other` on the original input. */
    def orElse(other: P[A, B]): P[A, B]

    /** Ordered choice tagging the alternative that succeeded: `self` on the left, `other` on the right. */
    def or[C](other: P[A, C]): P[A, B + C]

    /** Tries `self`; if it fails, succeeds without consuming anything, returning the semantic input on the right. */
    def optional: P[A, B + A] = self +> success[A]

  // ===========================================================================
  // 8. Predicates & Lookahead
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** Succeeds iff `self` succeeds, consuming nothing and returning the semantic input. */
    def lookahead: P[A, A]

    /** Succeeds iff `self` fails, consuming nothing and returning the semantic input: looks ahead at `self`, then fails
      * on the left alternative and succeeds on the right one.
      */
    def not: P[A, A] = (~self +> success[A]) >> (failure[A, A] || success[A])

  // ===========================================================================
  // 9. Iteration & Recursion
  // ===========================================================================

  extension [A, B](self: P[A, B + A])
    /** Runs `self` repeatedly, feeding each right result back as the next semantic input, until it yields a left
      * result.
      */
    def loop: P[A, B]

  extension [A, B](self: P[A, B])
    /** Runs `self` zero or more times until it fails, collecting the results. */
    def repeated: P[A, Many[B]]

    /** Runs `self` exactly `n` times, collecting the results. */
    def times(n: Int): P[A, Many[B]]

    /** Runs `self` at least `n` times until it fails, collecting the results. */
    def atLeast(n: Int): P[A, Many[B]]

    /** Runs `self` one or more times separated by `separator`, collecting the results of `self`. */
    def separatedBy[C](separator: P[A, C]): P[A, Many[B]]

  /** The parser defined recursively by `f`, which receives the parser being defined. */
  def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B]

  /** A tuple of mutually recursive parsers, solved one parser at a time via Bekić's theorem:
    *
    * fix(*x*, *y*) = (fix *x*. *f*₁(*x*, *y*₀), *y*₀) where *y*₀ = fix *y*. *f*₂(fix *x*. *f*₁(*x*, *y*), *y*).
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

  // ===========================================================================
  // Laws
  // ===========================================================================

  /** Equations between parsers, stated with the operations of the algebra alone.
    *
    * They hold for deterministic, backtracking (PEG-style) parsers. Notably absent are equations that such parsers
    * violate, e.g. `(p orElse q) andThen r == (p andThen r) orElse (q andThen r)`, since ordered choice commits to `p`.
    */
  object ParserLaws {

    /** Running `success` first changes nothing. */
    def leftIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (success[A] >> p) === p
    }

    /** Running `success` last changes nothing. */
    def rightIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (p >> success[B]) === p
    }

    /** Sequencing is associative. */
    def associativity[A, B, C, D](p: P[A, B], q: P[B, C], r: P[C, D])(using P[A, D] is Eq): Boolean = {
      ((p >> q) >> r) === (p >> (q >> r))
    }

    /** Zipping two `success` parsers is `success` on pairs. */
    def zipIdentity[A, C](using P[A * C, A * C] is Eq): Boolean = {
      (success[A] ** success[C]) === success[A * C]
    }

    /** Nothing runs after a failure. */
    def leftZero[A, B, C](p: P[B, C])(using P[A, C] is Eq): Boolean = {
      (failure[A, B] >> p) === failure[A, C]
    }

    /** A failure at the end fails the whole sequence. */
    def rightZero[A, B, C](p: P[A, B])(using P[A, C] is Eq): Boolean = {
      (p >> failure[B, C]) === failure[A, C]
    }

    /** A failing first alternative is skipped. */
    def choiceLeftIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (failure[A, B] |> p) === p
    }

    /** A failing last alternative is never needed. */
    def choiceRightIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (p |> failure[A, B]) === p
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
      (~p >> !p) === failure[A, A]
    }

    /** A recursive parser is its own unfolding. */
    def recursionUnfolding[A, B](f: P[A, B] => P[A, B])(using P[A, B] is Eq): Boolean = {
      recursive(f) === f(recursive(f))
    }

    /** A loop is one step followed by either stopping or looping again. */
    def loopUnfolding[A, B](p: P[A, B + A])(using P[A, B] is Eq): Boolean = {
      p.loop === (p >> (success[B] || p.loop))
    }
  }

  // ===========================================================================
  // Symbolic Aliases
  // ===========================================================================

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
}

/** Mixins implementing the operations of [[ParserAlgebra]].
  *
  * '''Structural mixins''' implement primitives from a categorical structure on `Self`, given as a `val` that the
  * interpreter provides. Each states which laws of that structure parsers satisfy and which they break:
  *   - [[Sequencing]]: `Self` is a promonad (parsers form a category)
  *   - [[Zipping]]: `Self` is strong (parsers form a premonoidal category)
  *   - [[Branching]]: `Self` is cocartesian (parsers have coproducts)
  *   - [[Alternation]]: `Self` is enriched in additive monoids (parsers can be added)
  *   - [[Lookahead]]: `Self` is a restriction promonad (parsers form a restriction category)
  *   - [[Looping]]: `Self` is an Elgot promonad (parsers can be iterated)
  *   - [[Recursion]]: `Self` is enriched in types with fixed points (parsers can be defined recursively)
  *
  * '''Derived mixins''' implement the remaining combinators from the operations of the algebra, requiring some
  * structure on `On`: [[Pairing]] and [[Iteration]]. Combinators that require nothing at all (`optional`, `not`) are
  * defined in [[ParserAlgebra]] itself.
  *
  * The lexical and structural primitives (`rule`, `literal`, `regex`) are left to interpreters.
  */
object ParserAlgebra {

  /** Summons the `ParserAlgebra` instance of `P`. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = summon

  // ===========================================================================
  // Structural mixins
  // ===========================================================================

  /** Implements `pure`, `success`, `andThen`, `map` and `mapInput` from a promonad structure on `Self` over `On`:
    *   - `pure` is the unit *η*, `success` the identity and `andThen` the composition of the induced category
    *   - `map` and `mapInput` are the profunctorial actions *P*(*id*, *g*) and *P*(*f*, *id*)
    *
    * All promonad laws hold.
    */
  trait Sequencing extends ParserAlgebra {
    val SelfIsPromonad: Self is Promonad on On
    import SelfIsPromonad.*

    override def pure[A, B](f: A ==> B): P[A, B] = unit(f)

    override def success[A]: P[A, A] = identity[A]

    extension [A, B](self: P[A, B])
      override def andThen[C](other: P[B, C]): P[A, C] = self >>> other

      override def map[D](g: B ==> D): P[A, D] = self.rmap(g)

      override def mapInput[C](f: C ==> A): P[C, B] = self.lmap(f)
  }

  /** Implements `zip` from a strength of `Self` with respect to (`Pair`, `Empty`) on `On`: *p* ⊗ *q* = *first*(*p*) ⨾
    * *second*(*q*).
    *
    * Parsers form a premonoidal, not a monoidal, category: ⊗ is functorial in each argument separately but not jointly.
    * The interchange law (*p* ⊗ *q*) ⨾ (*r* ⊗ *s*) = (*p* ⨾ *r*) ⊗ (*q* ⨾ *s*) fails, because the left-hand side runs
    * `q` before `r` and the right-hand side runs `r` before `q`. It holds when `q` or `r` is central, e.g. pure.
    */
  trait Zipping extends ParserAlgebra {
    val SelfIsStrong: Self is Strong.on[On, Empty, Pair]
    import SelfIsStrong.{first, second}

    extension [A, B](self: P[A, B])
      override def zip[C, D](other: P[C, D]): P[A * C, B * D] = self.first[C] >> other.second[B]
  }

  /** Implements `branch`, `merge` and `or` from coproducts (`Alternative`, `None`) on the category of parsers:
    *   - `branch` is the coproduct *p* ⊕ *q* and `merge` the copairing [*p*, *q*]
    *   - `or` tags the alternatives of `orElse` with the injections *ι*₁ and *ι*₂
    *
    * All cocartesian laws hold: exactly one of the branches runs, so no ordering issue arises.
    */
  trait Branching extends ParserAlgebra {
    val SelfIsCocartesian: Self is Cocartesian.`with`[None, Alternative]
    import SelfIsCocartesian.{+++, left, right, |||}

    extension [A, B](self: P[A, B])
      override def branch[C, D](other: P[C, D]): P[A + C, B + D] = self +++ other

      override def merge[C](other: P[C, B]): P[A + C, B] = self ||| other

      override def or[C](other: P[A, C]): P[A, B + C] = (self >> left[B, C]) |> (other >> right[B, C])
  }

  /** Implements `failure` and `orElse` from an enrichment of `Self` in additive monoids: `failure` is 0 and `orElse` is
    * +.
    *
    * Ordered choice is a monoid with `failure` as its unit, and `failure` is a zero of `andThen` on both sides.
    * However, composition distributes over choice only on one side: *r* ⨾ (*p* + *q*) = (*r* ⨾ *p*) + (*r* ⨾ *q*)
    * holds, but (*p* + *q*) ⨾ *r* = (*p* ⨾ *r*) + (*q* ⨾ *r*) fails because choice commits to `p` once it succeeds,
    * even if `r` then fails. Choice is also not commutative.
    */
  trait Alternation extends ParserAlgebra {
    val SelfIsAdditive: Self is Enriched over Monoid.Additive
    import SelfIsAdditive.HomIsV

    override def failure[A, B]: P[A, B] = HomIsV[A, B].zero

    extension [A, B](self: P[A, B])
      override def orElse(other: P[A, B]): P[A, B] = self + other
  }

  /** Implements `lookahead` as the restriction p̄ of a restriction category: the partial identity defined exactly where
    * `p` succeeds.
    *
    * All restriction laws hold for deterministic parsers.
    */
  trait Lookahead extends ParserAlgebra {
    val SelfIsRestriction: Self is Restriction
    import SelfIsRestriction.restrict

    extension [A, B](self: P[A, B])
      override def lookahead: P[A, A] = self.restrict
  }

  /** Implements `loop` as the Elgot iteration *p*† with respect to (`Alternative`, `None`) on `On`.
    *
    * The fixed point, naturality and codiagonal laws hold. Iteration is a least fixed point, so a step that keeps
    * yielding on the right diverges rather than fails.
    */
  trait Looping extends ParserAlgebra {
    val SelfIsElgot: Self is Elgot.on[On, None, Alternative]
    import SelfIsElgot.dagger

    extension [A, B](self: P[A, B + A])
      override def loop: P[A, B] = self.dagger
  }

  /** Implements `recursive` as the fixed point of `f` in the hom-set of parsers, which is enriched in types with a
    * Conway fixed-point operator.
    *
    * The Conway laws hold: the fixed point, dinaturality and diagonal properties, which also justify solving mutual
    * recursion one parser at a time by Bekić's theorem. For the least fixed point, unguarded (left) recursion
    * diverges. Interpreters supporting left recursion by growing a seed from `failure` compute a different fixed
    * point, which breaks these laws when ordered choice or negation make the definition non-monotone.
    */
  trait Recursion extends ParserAlgebra {
    val SelfIsFixed: Self is Enriched over Conway.Fixed
    import SelfIsFixed.HomIsV

    override def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B] = HomIsV[A, B].fix(f)
  }

  // ===========================================================================
  // Derived mixins
  // ===========================================================================

  /** Implements shared-input sequencing from `zip` by duplicating the semantic input and projecting results. Requires:
    * `On` is cartesian with respect to (`Pair`, `Empty`).
    *
    * `pair` is not a categorical product of parsers: projecting one component of `p.pair(q)` still runs (and may fail
    * on) the other.
    */
  trait Pairing extends ParserAlgebra {
    val OnIsCartesian: On is Cartesian.`with`[Empty, Pair]
    import OnIsCartesian.{`*` as _, *}

    extension [A, B](self: P[A, B])
      override def pair[C](other: P[A, C]): P[A, B * C] = (self ** other).mapInput(diagonal[A])

      override def skipThen[C](other: P[A, C]): P[A, C] = (self && other).map(second[B, C])

      override def thenSkip[C](other: P[A, C]): P[A, B] = (self && other).map(first[B, C])

      override def between[C, D](open: P[A, C], close: P[A, D]): P[A, B] = open *> self <* close
  }

  /** Implements the repetition combinators with `loop`, threading the semantic input and the results so far.
    *
    * Requires: `On` is cartesian with respect to (`Pair`, `Empty`) and cocartesian with respect to (`Alternative`,
    * `None`), and `Many` supports
    *   - [[nil]]: the empty collection
    *   - [[snoc]]: appending a result
    *
    * Repeating a parser that succeeds without consuming input diverges.
    */
  trait Iteration extends ParserAlgebra {
    val OnIsCartesian: On is Cartesian.`with`[Empty, Pair]
    val OnIsCocartesian: On is Cocartesian.`with`[None, Alternative]
    import OnIsCartesian.*
    import OnIsCartesian.SelfIsPromonad.{>>>, identity}
    import OnIsCocartesian.{left, right}

    /** The empty collection. */
    def nil[B]: Empty ==> Many[B]

    /** Appends a result to a collection. */
    def snoc[B]: (Many[B] * B) ==> Many[B]

    /** Pairs the semantic input with the empty collection. */
    private def start[A, B]: P[A, A * Many[B]] = pure(identity[A] &&& (augment[A] >>> nil[B]))

    /** Runs `item` once, appending its result: (*a*, *bs*) ↦ (*a*, *bs* :+ *item*(*a*)). */
    private def step[A, B](item: P[A, B]): P[A * Many[B], A * Many[B]] = {
      val reshape = first[A, Many[B]] &&& (second[A, Many[B]] &&& first[A, Many[B]])
      val finish  = identity[A] *** snoc[B]
      (success[A] ** (success[Many[B]] ** item)).mapInput(reshape).map(finish)
    }

    /** Runs `seed`, then `item` until it fails. */
    private def iterate[A, B](seed: P[A, A * Many[B]], item: P[A, B]): P[A, Many[B]] = {
      val next = step(item).map(right[Many[B], A * Many[B]])
      val done = pure(second[A, Many[B]] >>> left[Many[B], A * Many[B]])
      seed >> (next |> done).loop
    }

    /** Runs `item` exactly `n` times. */
    private def unrolled[A, B](item: P[A, B], n: Int): P[A, A * Many[B]] = {
      require(n >= 0, "n must be non-negative")
      (0 until n).foldLeft(start[A, B])((acc, _) => acc >> step(item))
    }

    extension [A, B](self: P[A, B])
      override def repeated: P[A, Many[B]] = iterate(start[A, B], self)

      override def times(n: Int): P[A, Many[B]] = unrolled(self, n).map(second[A, Many[B]])

      override def atLeast(n: Int): P[A, Many[B]] = iterate(unrolled(self, n), self)

      override def separatedBy[C](separator: P[A, C]): P[A, Many[B]] = iterate(unrolled(self, 1), separator *> self)
  }
}
