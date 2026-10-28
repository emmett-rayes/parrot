package parrot
package category

/** A law-checking oracle for a preorder: the inequational counterpart of [[Observable]].
  *
  * Represents a test of order, where
  *   - ⊑ is a decidable preorder that fails only if some observation orders the two values apart
  *
  * Inequational laws, such as "running a parser before a failure only adds information", are checked with it.
  */
trait Preorder extends caps.Pure {
  type Self

  /** Returns `false` if some observation shows that *a* ⊑ *b* fails. */
  def below(a: Self, b: Self): Boolean

  extension (a: Self)
    /** Infix form of [[below]]. */
    final def <~(b: Self): Boolean = {
      Preorder.this.below(a, b)
    }

  /** Laws that any `Preorder` must satisfy: those of a preorder that orders equal and agreeing values both ways. */
  object PreorderLaws {

    /** *a* ⊑ *a* */
    def reflexivity(a: Self): Boolean = {
      a <~ a
    }

    /** If *a* ⊑ *b* and *b* ⊑ *c*, then *a* ⊑ *c* */
    def transitivity(a: Self, b: Self, c: Self): Boolean = {
      !(a <~ b && b <~ c) || (a <~ c)
    }

    /** If *a* = *a*₂, then *a* ⊑ *a*₂ and *a*₂ ⊑ *a*: no observation orders equal values apart.
      *
      * @note The premise is not checked: *a*₂ must be equal to *a* by construction, a variant such as an η-expansion.
      */
    def soundness(a: Self, a2: Self): Boolean = {
      (a <~ a2) && (a2 <~ a)
    }

    /** If *a* ≟ *b*, then *a* ⊑ *b*: an equation that holds also holds as an inequation.
      *
      * @note The `Observable` must make the observations of the preorder, at the same sample points: agreement at some
      *   points says nothing about the order at others.
      */
    def agreement(a: Self, b: Self)(using Self is Observable): Boolean = {
      !(a =?= b) || (a <~ b)
    }
  }
}

object Preorder {

  /** Summons the `Preorder` instance of `A`. */
  def apply[A: Preorder]: A is Preorder = summon

  /** The order of a semilattice in 𝒮: *a* ⊑ *b* when *a* ⊔ *b* = *b*. */
  def of(L: Semilattice { val V: Total.Product.type })(using L.M is Eq): L.M is Preorder = {
    new Preorder {
      type Self = L.M

      def below(a: L.M, b: L.M): Boolean = {
        L.multiply((a, b)) === b
      }
    }
  }

  /** Observes a value through finitely many observations: *a* ⊑ *b* when every observation is ordered so. */
  def through[A, O: Preorder](observations: List[A -> O]): A is Preorder = {
    new Preorder {
      type Self = A

      def below(a: A, b: A): Boolean = {
        observations.forall(o => o(a) <~ o(b))
      }
    }
  }
}
