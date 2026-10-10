package parrot
package parser

import parrot.category.{Cartesian, Cocartesian, Eq, Promonad}

import scala.util.matching.Regex

/** An assumption-free algebra of parsers.
  *
  * A parser *p*: *P*[*A*, *B*] consumes a prefix of the input while transforming a semantic input *A* into a semantic
  * result *B*. The algebra only *declares* its carrier, its objects and its operations; it imposes no categorical
  * structure on any of them. Derived combinators are provided by the mixins in [[ParserAlgebra$ ParserAlgebra]], each of
  * which states exactly the structure it relies on, so that an interpreter can choose between the generic derivation
  * and a specialized primitive on a per-combinator basis.
  *
  * The abstract objects are
  *   - *P* = `Self`, the carrier of parsers
  *   - ==> = `On`, the base category of pure adaptations embedded into *P* by [[pure]]
  *   - ⊗ = `Tensor` with unit *I*, the (premonoidal) product used by sequencing
  *   - ⊕ = `Coproduct` with unit *Z*, the coproduct used by branching and choice
  *   - `Many`, the list object used by iteration
  *
  * @note
  *   ⊗ is *premonoidal*, not monoidal: [[zip]] runs its operands in order on a shared input stream, so the interchange
  *   law (*p* ⊗ *q*) ⨾ (*r* ⊗ *s*) = (*p* ⨾ *r*) ⊗ (*q* ⨾ *s*) only holds for central (non-consuming) parsers.
  */
trait ParserAlgebra {

  /** The carrier of parsers. */
  type Self[_, _]
  final type P = Self

  /** The base category of pure adaptations. */
  type On[_, _]
  final type ==> = On

  /** The unit object *I* of ⊗. */
  type I

  /** The tensor product ⊗ on objects. */
  type Tensor[_, _]
  final type * = Tensor

  /** The unit object *Z* of ⊕. */
  type Z

  /** The coproduct ⊕ on objects. */
  type Coproduct[_, _]
  final type + = Coproduct

  /** The list object *B*\* used to collect the results of iteration. */
  type Many[_]

  // ===========================================================================
  // 1. Structural / Metadata
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** Associates `self` with the named rule `label` (for diagnostics, memoization, tracing). Semantically the
      * identity.
      */
    def rule(label: String): P[A, B]

  // ===========================================================================
  // 2. Lexical / Primitive Matchers
  // ===========================================================================

  /** Consumes `expected` at the current position. */
  def literal(expected: String): P[I, String]

  /** Consumes a match of `expected` anchored at the current position. */
  def regex(expected: Regex): P[I, String]

  // ===========================================================================
  // 3. Embedding / Adaptation
  // ===========================================================================

  /** Embeds a morphism of the base category as a parser that consumes no input (the unit *η*: ==> ⇒ *P*). */
  def pure[A, B](f: A ==> B): P[A, B]

  extension [A, B](self: P[A, B])
    /** Adapts the semantic input by *f* and the semantic result by *g*. */
    def dimap[C, D](f: C ==> A, g: B ==> D): P[C, D]

    /** Adapts the semantic input by *f*. */
    def lmap[C](f: C ==> A): P[C, B]

    /** Adapts the semantic result by *g*. */
    def rmap[D](g: B ==> D): P[A, D]

  // ===========================================================================
  // 4. Sequential Composition
  // ===========================================================================

  /** The identity *id*\_*A*: *A* ~> *A*; succeeds without consuming input, returning its semantic input. */
  def success[A]: P[A, A]

  extension [A, B](self: P[A, B])
    /** Sequential composition *self* ⨾ *other*: feeds the result of `self` to `other` on the remaining input. */
    def andThen[C](other: P[B, C]): P[A, C]

  // ===========================================================================
  // 5. Parallel / Product Composition
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** The premonoidal product *self* ⊗ *other*: runs `self` on the left input, then `other` on the right input. */
    def zip[C, D](other: P[C, D]): P[A * C, B * D]

    /** Left strength: *self* ⊗ *id*\_*C*. */
    def first[C]: P[A * C, B * C]

    /** Right strength: *id*\_*C* ⊗ *self*. */
    def second[C]: P[C * A, C * B]

    /** Runs `self` then `other` on a shared input, pairing their results. */
    def pair[C](other: P[A, C]): P[A, B * C]

    /** Runs `self` then `other` on a shared input, keeping the result of `other`. */
    def skipThen[C](other: P[A, C]): P[A, C]

    /** Runs `self` then `other` on a shared input, keeping the result of `self`. */
    def thenSkip[C](other: P[A, C]): P[A, B]

    /** Runs `open`, `self`, `close` on a shared input, keeping the result of `self`. */
    def between[C, D](open: P[A, C], close: P[A, D]): P[A, B]

  // ===========================================================================
  // 6. Branching / Coproduct Composition
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** The coproduct *self* ⊕ *other*: dispatches on the semantic input. */
    def branch[C, D](other: P[C, D]): P[A + C, B + D]

    /** The copairing [*self*, *other*]: dispatches on the semantic input into a common result. */
    def merge[C](other: P[C, B]): P[A + C, B]

  // ===========================================================================
  // 7. Alternative / Choice
  // ===========================================================================

  /** The parser that always fails; the unit of [[orElse]] and a zero of [[andThen]]. */
  def failure[A, B]: P[A, B]

  extension [A, B](self: P[A, B])
    /** Ordered choice: tries `self`, falling back to `other` on the original input if `self` fails. */
    def orElse(other: P[A, B]): P[A, B]

    /** Ordered choice tagging the branch taken: `self` on the left, `other` on the right. */
    def either[C](other: P[A, C]): P[A, B + C]

    /** Tries `self`; on failure succeeds without consuming input, returning the semantic input on the right.
      *
      * Endomorphic on failure (*B* ⊕ *A* rather than *B* ⊕ *I*) so that no terminal morphism *A* ==> *I* is needed.
      */
    def optional: P[A, B + A]

  // ===========================================================================
  // 8. Predicates & Lookahead
  // ===========================================================================

  extension [A, B](self: P[A, B])
    /** Positive lookahead: succeeds iff `self` succeeds, consuming nothing and returning the semantic input.
      *
      * This is the restriction p̄: *A* ~> *A* of a restriction category (see [[parrot.category.Restriction]]).
      */
    def lookahead: P[A, A]

    /** Negative lookahead: succeeds iff `self` fails, consuming nothing and returning the semantic input. */
    def not: P[A, A]

  // ===========================================================================
  // 9. Iteration & Recursion
  // ===========================================================================

  extension [A, B](self: P[A, B + A])
    /** The Elgot iteration *self*†: repeats `self` while it yields on the right, stopping when it yields on the left.
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

  /** The fixed point of `f`. */
  def recursive[A, B](f: P[A, B] => P[A, B]): P[A, B]

  /** The simultaneous fixed point of a tuple of mutually recursive parsers, reduced to unary fixed points via Bekić's
    * theorem: fix(*x*, *y*) = (fix *x*. *f*₁(*x*, *y*₀), *y*₀) where *y*₀ = fix *y*. *f*₂(fix *x*. *f*₁(*x*, *y*), *y*).
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

  /** Laws stated purely in terms of the operations of the algebra; they hold in every lawful interpreter. */
  object ParserLaws {

    /** *id* ⨾ *p* = *p* */
    def leftIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (success[A] >> p) === p
    }

    /** *p* ⨾ *id* = *p* */
    def rightIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (p >> success[B]) === p
    }

    /** (*p* ⨾ *q*) ⨾ *r* = *p* ⨾ (*q* ⨾ *r*) */
    def associativity[A, B, C, D](p: P[A, B], q: P[B, C], r: P[C, D])(using P[A, D] is Eq): Boolean = {
      ((p >> q) >> r) === (p >> (q >> r))
    }

    /** *id* ⊗ *id* = *id* */
    def zipIdentity[A, C](using P[A * C, A * C] is Eq): Boolean = {
      (success[A] ** success[C]) === success[A * C]
    }

    /** ⊥ ⨾ *p* = ⊥ */
    def leftZero[A, B, C](p: P[B, C])(using P[A, C] is Eq): Boolean = {
      (failure[A, B] >> p) === failure[A, C]
    }

    /** *p* ⨾ ⊥ = ⊥ */
    def rightZero[A, B, C](p: P[A, B])(using P[A, C] is Eq): Boolean = {
      (p >> failure[B, C]) === failure[A, C]
    }

    /** ⊥ + *p* = *p* */
    def choiceLeftIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (failure[A, B] +> p) === p
    }

    /** *p* + ⊥ = *p* */
    def choiceRightIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (p +> failure[A, B]) === p
    }

    /** (*p* + *q*) + *r* = *p* + (*q* + *r*) */
    def choiceAssociativity[A, B](p: P[A, B], q: P[A, B], r: P[A, B])(using P[A, B] is Eq): Boolean = {
      ((p +> q) +> r) === (p +> (q +> r))
    }

    /** (R1) p̄ ⨾ *p* = *p* */
    def lookaheadIdentity[A, B](p: P[A, B])(using P[A, B] is Eq): Boolean = {
      (~p >> p) === p
    }

    /** (R2) p̄ ⨾ q̄ = q̄ ⨾ p̄ */
    def lookaheadCommutativity[A, B, C](p: P[A, B], q: P[A, C])(using P[A, A] is Eq): Boolean = {
      (~p >> ~q) === (~q >> ~p)
    }

    /** (R3) (p̄ ⨾ *q*)‾ = p̄ ⨾ q̄ */
    def lookaheadCompose[A, B, C](p: P[A, B], q: P[A, C])(using P[A, A] is Eq): Boolean = {
      ~(~p >> q) === (~p >> ~q)
    }

    /** (R4) *p* ⨾ q̄ = (*p* ⨾ *q*)‾ ⨾ *p* */
    def lookaheadPrecompose[A, B, C](p: P[A, B], q: P[B, C])(using P[A, B] is Eq): Boolean = {
      (p >> ~q) === (~(p >> q) >> p)
    }

    /** !!*p* = &*p* */
    def doubleNegation[A, B](p: P[A, B])(using P[A, A] is Eq): Boolean = {
      !(!p) === ~p
    }

    /** &*p* ⨾ !*p* = ⊥ */
    def negationExclusion[A, B](p: P[A, B])(using P[A, A] is Eq): Boolean = {
      (~p >> !p) === failure[A, A]
    }

    /** *p*† = *p* ⨾ [*id*, *p*†] */
    def loopFixedPoint[A, B](p: P[A, B + A])(using P[A, B] is Eq): Boolean = {
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
    def >*[C](other: P[A, C]): P[A, B] = self.thenSkip(other)

    /** Alias for [[branch]]. */
    def ++[C, D](other: P[C, D]): P[A + C, B + D] = self.branch(other)

    /** Alias for [[merge]]. */
    def ||[C](other: P[C, B]): P[A + C, B] = self.merge(other)

    /** Alias for [[orElse]]. */
    def +>(other: P[A, B]): P[A, B] = self.orElse(other)

    /** Alias for [[either]]. */
    def |>[C](other: P[A, C]): P[A, B + C] = self.either(other)

    /** Alias for [[lookahead]]. */
    def unary_~ : P[A, A] = self.lookahead

    /** Alias for [[not]]. */
    def unary_! : P[A, A] = self.not
}

/** Mixins deriving combinators of [[ParserAlgebra]], each requiring only the structure named in its documentation. */
object ParserAlgebra {

  /** Summons the `ParserAlgebra` instance of `P`. */
  def apply[P[_, _]: ParserAlgebra]: P is ParserAlgebra = summon

  // ===========================================================================
  // Requirements on the base category
  // ===========================================================================

  /** Requires the base category to be a category (a promonad). */
  trait OnPromonad extends ParserAlgebra {
    val OnIsPromonad: On is Promonad
  }

  /** Requires the base category to be cartesian with respect to (⊗, *I*). */
  trait OnCartesian extends ParserAlgebra {
    val OnIsCartesian: On is Cartesian.`with`[I, Tensor]
  }

  /** Requires the base category to be cocartesian with respect to (⊕, *Z*). */
  trait OnCocartesian extends ParserAlgebra {
    val OnIsCocartesian: On is Cocartesian.`with`[Z, Coproduct]
  }

  // ===========================================================================
  // Derivations
  // ===========================================================================

  /** Derives [[lmap]] and [[rmap]] from a primitive [[dimap]]. Requires: ==> is a category. */
  trait Profunctorial extends OnPromonad {
    extension [A, B](self: P[A, B])
      override def lmap[C](f: C ==> A): P[C, B] = self.dimap(f, OnIsPromonad.identity[B])

      override def rmap[D](g: B ==> D): P[A, D] = self.dimap(OnIsPromonad.identity[A], g)
  }

  /** Derives [[dimap]], [[lmap]] and [[rmap]] from [[pure]] and [[andThen]]. Requires: nothing. */
  trait Mapping extends ParserAlgebra {
    extension [A, B](self: P[A, B])
      override def dimap[C, D](f: C ==> A, g: B ==> D): P[C, D] = pure(f).andThen(self).andThen(pure(g))

      override def lmap[C](f: C ==> A): P[C, B] = pure(f).andThen(self)

      override def rmap[D](g: B ==> D): P[A, D] = self.andThen(pure(g))
  }

  /** Derives the strengths [[first]] and [[second]] from [[zip]] and [[success]]. Requires: nothing. */
  trait Zipping extends ParserAlgebra {
    extension [A, B](self: P[A, B])
      override def first[C]: P[A * C, B * C] = self.zip(success[C])

      override def second[C]: P[C * A, C * B] = success[C].zip(self)
  }

  /** Derives shared-input sequencing from [[zip]] via the diagonal and projections. Requires: ==> is cartesian. */
  trait Pairing extends OnCartesian {
    extension [A, B](self: P[A, B])
      override def pair[C](other: P[A, C]): P[A, B * C] = self.zip(other).lmap(OnIsCartesian.diagonal[A])

      override def skipThen[C](other: P[A, C]): P[A, C] = self.pair(other).rmap(OnIsCartesian.second[B, C])

      override def thenSkip[C](other: P[A, C]): P[A, B] = self.pair(other).rmap(OnIsCartesian.first[B, C])

      override def between[C, D](open: P[A, C], close: P[A, D]): P[A, B] = open.skipThen(self.thenSkip(close))
  }

  /** Derives [[either]] from [[orElse]] via the injections, and [[merge]] from [[branch]] via the codiagonal.
    * Requires: ==> is cocartesian.
    */
  trait AlternativeBranching extends OnCocartesian {
    extension [A, B](self: P[A, B])
      override def either[C](other: P[A, C]): P[A, B + C] = {
        self.rmap(OnIsCocartesian.left[B, C]).orElse(other.rmap(OnIsCocartesian.right[B, C]))
      }

      override def merge[C](other: P[C, B]): P[A + C, B] = self.branch(other).rmap(OnIsCocartesian.fold[B])
  }

  /** Derives [[optional]] from [[either]] and [[success]]. Requires: nothing. */
  trait Optional extends ParserAlgebra {
    extension [A, B](self: P[A, B])
      override def optional: P[A, B + A] = self.either(success[A])
  }

  /** Derives [[not]] from [[lookahead]], [[either]], [[merge]], [[failure]] and [[success]]: !*p* = (&*p* | *id*) ⨾
    * [⊥, *id*]. Requires: nothing.
    */
  trait Negation extends ParserAlgebra {
    extension [A, B](self: P[A, B])
      override def not: P[A, A] = self.lookahead.either(success[A]).andThen(failure[A, A].merge(success[A]))
  }

  /** Derives the iteration combinators from [[loop]], threading the state *A* ⊗ *B*\* through the loop.
    *
    * Requires: ==> is cartesian and cocartesian, and `Many` is a list object, i.e. it is equipped with
    *   - [[nil]]: *I* ==> *B*\*
    *   - [[snoc]]: *B*\* ⊗ *B* ==> *B*\*
    */
  trait Iteration extends OnCartesian, OnCocartesian {

    /** The empty list. */
    def nil[B]: I ==> Many[B]

    /** Appends an element to a list. */
    def snoc[B]: (Many[B] * B) ==> Many[B]

    /** ⟨*id*, *nil* ∘ !⟩: *A* ~> *A* ⊗ *B*\* */
    private def start[A, B]: P[A, A * Many[B]] = {
      val C = OnIsCartesian
      pure(C.product(C.SelfIsPromonad.identity[A], C.SelfIsPromonad.andThen(C.augment[A], nil[B])))
    }

    /** One step (*a*, *bs*) ↦ (*a*, *bs* :+ *item*(*a*)). */
    private def step[A, B](item: P[A, B]): P[A * Many[B], A * Many[B]] = {
      val C       = OnIsCartesian
      val reshape = C.product(C.first[A, Many[B]], C.product(C.second[A, Many[B]], C.first[A, Many[B]]))
      val finish  = C.tensor(C.SelfIsPromonad.identity[A], snoc[B])
      success[A].zip(success[Many[B]].zip(item)).dimap(reshape, finish)
    }

    /** `seed` followed by `item` repeated until it fails. */
    private def iterate[A, B](seed: P[A, A * Many[B]], item: P[A, B]): P[A, Many[B]] = {
      val C    = OnIsCartesian
      val K    = OnIsCocartesian
      val next = step(item).rmap(K.right[Many[B], A * Many[B]])
      val done = pure(K.SelfIsPromonad.andThen(C.second[A, Many[B]], K.left[Many[B], A * Many[B]]))
      seed.andThen(next.orElse(done).loop)
    }

    /** `start` followed by exactly `n` steps of `item`. */
    private def unrolled[A, B](item: P[A, B], n: Int): P[A, A * Many[B]] = {
      require(n >= 0, "n must be non-negative")
      (0 until n).foldLeft(start[A, B])((acc, _) => acc.andThen(step(item)))
    }

    extension [A, B](self: P[A, B])
      override def repeated: P[A, Many[B]] = iterate(start[A, B], self)

      override def times(n: Int): P[A, Many[B]] = unrolled(self, n).rmap(OnIsCartesian.second[A, Many[B]])

      override def atLeast(n: Int): P[A, Many[B]] = iterate(unrolled(self, n), self)

      override def separatedBy[C](separator: P[A, C]): P[A, Many[B]] = {
        iterate(unrolled(self, 1), separator.skipThen(self))
      }
  }
}
