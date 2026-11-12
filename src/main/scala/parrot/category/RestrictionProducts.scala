package parrot
package category

/** A restriction product structure on a restriction category **C**.
  *
  * Represents binary restriction products (Cockett–Lack), on a symmetric monoidal structure (**C**, ⊗, *I*), where
  *   - *π*₁: *A* ⊗ *B* → *A* and *π*₂: *A* ⊗ *B* → *B* are the projections, which are total
  *   - ⟨*f*,*g*⟩: *X* → *A* ⊗ *B* is the pairing, defined where both *f* and *g* are
  *
  * A projection of a pairing is a component only where the other component is defined. Where every morphism is
  * total, restriction products are products.
  */
abstract class RestrictionProducts(
  tracked val restriction: Restriction,
  tracked val monoidal: Symmetric.On[restriction.category.type],
) extends caps.Pure {
  import monoidal.`*`
  import restriction.{category, restrict}
  import category.{Obj, identity, -->, >>>}

  /** The first projection *π*₁: *A* ⊗ *B* → *A*. */
  def fst[A: Obj, B: Obj]: (A * B) --> A

  /** The second projection *π*₂: *A* ⊗ *B* → *B*. */
  def snd[A: Obj, B: Obj]: (A * B) --> B

  /** The pairing ⟨*f*,*g*⟩: *X* → *A* ⊗ *B* of *f*: *X* → *A* and *g*: *X* → *B*. */
  def pair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B): X --> (A * B)

  /** Laws that any `RestrictionProducts` structure must satisfy. */
  object RestrictionProductsLaws {
    private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = monoidal.tensor.objects[A, B]

    /** *π*₁ ∘ ⟨*f*,*g*⟩ = *f* ∘ *ḡ*
      */
    def fstPair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(using (X --> A) is Observable): Boolean = {
      (pair(f, g) >>> fst[A, B]) =?= (restrict(g) >>> f)
    }

    /** *π*₂ ∘ ⟨*f*,*g*⟩ = *g* ∘ *f̄*
      */
    def sndPair[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(using (X --> B) is Observable): Boolean = {
      (pair(f, g) >>> snd[A, B]) =?= (restrict(f) >>> g)
    }

    /** ⟨*f*,*g*⟩‾ = *f̄* ∘ *ḡ*
      */
    def pairRestriction[X: Obj, A: Obj, B: Obj](f: X --> A, g: X --> B)(using (X --> X) is Observable): Boolean = {
      restrict(pair(f, g)) =?= (restrict(g) >>> restrict(f))
    }

    /** *π*₁‾ = *id* and *π*₂‾ = *id*: the projections are total.
      */
    def projectionsTotal[A: Obj, B: Obj](using ((A * B) --> (A * B)) is Observable): Boolean = {
      (restrict(fst[A, B]) =?= identity[A * B]) && (restrict(snd[A, B]) =?= identity[A * B])
    }

    /** ⟨*π*₁ ∘ *h*,*π*₂ ∘ *h*⟩ = *h*: a morphism into a restriction product is determined by its components.
      */
    def pairUniqueness[X: Obj, A: Obj, B: Obj](h: X --> (A * B))(using (X --> (A * B)) is Observable): Boolean = {
      pair(h >>> fst[A, B], h >>> snd[A, B]) =?= h
    }

    /** If *f* = *f*′ and *g* = *g*′, then ⟨*f*,*g*⟩ = ⟨*f*′,*g*′⟩.
      *
      * @note The premise is not checked: *f*′ and *g*′ must be equal to *f* and *g* by construction.
      */
    def pairCongruence[X: Obj, A: Obj, B: Obj](f: X --> A, f2: X --> A, g: X --> B, g2: X --> B)(
      using (X --> (A * B)) is Observable
    ): Boolean = {
      pair(f, g) =?= pair(f2, g2)
    }
  }
}

object RestrictionProducts {

  /** The restriction product structures on a restriction category with the restriction *R*. */
  type On[R <: Restriction] = RestrictionProducts { val restriction: R }
}
