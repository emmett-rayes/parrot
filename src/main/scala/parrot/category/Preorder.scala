package parrot
package category

/** An oracle for checking observational order.
  *
  * Represents a test of order, where
  *   - ⊑ is a decidable preorder that fails only if some observation orders the two values apart
  */
trait Preorder extends caps.Pure {
  type Self

  /** Returns `false` if some observation shows that *a* is not below *b*. */
  def below(a: Self, b: Self): Boolean

  extension (a: Self)
    /** Infix extension for [[below]]. */
    final def ?<(b: Self): Boolean = {
      Preorder.this.below(a, b)
    }

  /** Laws that any `Preorder` must satisfy.
    *
    * A preorder is a reflexive and transitive relation that orders equal and agreeing values both ways.
    */
  object PreorderLaws {
    extension (p: Boolean)
      private def implies(q: Boolean): Boolean = {
        !p || q
      }

    /** *a* ⊑ *a*
      */
    def reflexivity(a: Self): Boolean = {
      a ?< a
    }

    /** If *a* ⊑ *b* and *b* ⊑ *c*, then *a* ⊑ *c* */
    def transitivity(a: Self, b: Self, c: Self): Boolean = {
      (a ?< b && b ?< c) `implies` (a ?< c)
    }

    /** If *a*₁ = *a*₂, then *a*₁ ⊑ *a*₂ and *a*₂ ⊑ *a*₁
      *
      * No observation orders equal values apart.
      *
      * @note The premise is not checked: *a*₂ must be equal to *a*₁ by construction.
      */
    def soundness(a1: Self, a2: Self): Boolean = {
      (a1 ?< a2) && (a2 ?< a1)
    }

    /** If *a* ≟ *b*, then *a* ⊑ *b* and *b* ⊑ *a*
      *
      * No observation orders agreeing values apart.
      *
      * @note The `Observable` must make the observations of the preorder, at the same sample points. Agreement at some
      *   points says nothing about the order at others.
      */
    def agreement(a: Self, b: Self)(using Self is Observable): Boolean = {
      (a =?= b) `implies` ((a ?< b) && (b ?< a))
    }
  }
}

object Preorder {

  /** Summons the `Preorder` instance of `A`. */
  def apply[A: Preorder]: A is Preorder = summon

  /** The order of a semilattice in 𝒮: *a* ⊑ *b* when *a* ⊔ *b* = *b*. */
  def of(L: Semilattice { val V: Total.Product.type })(using L.M is Eq): L.M is Preorder = {
    new Preorder {
      import L.M
      type Self = M

      def below(a: M, b: M): Boolean = {
        L.multiply((a, b)) === b
      }
    }
  }

  /** Observes a value through finitely many observations: *a* ⊑ *b* when every observation is ordered so. */
  def through[A, O: Preorder](observations: List[A -> O]): A is Preorder = {
    new Preorder {
      type Self = A

      def below(a: A, b: A): Boolean = {
        observations.forall(o => o(a) ?< o(b))
      }
    }
  }
}
