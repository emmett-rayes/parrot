package parrot
package category

/** A symmetric structure on a premonoidal category **C**.
  *
  * Represents a symmetric premonoidal category, where
  *   - *σ*: *A* ⊗ *B* ≅ *B* ⊗ *A* is the braiding
  *
  * The braiding is central, natural in each component separately and its own inverse. Symmetry is independent of
  * monoidality: a Freyd category is symmetric without being monoidal ([[Freyd]]), and a monoidal category with a
  * braiding is a [[Symmetric]] category.
  *
  * @note A trait with [[Premonoidal]] as its self-type, mixed into the premonoidal classes that are symmetric:
  *   [[Symmetric]] and [[Freyd]].
  * @see docs/TUTORIAL.md §17.4
  */
trait SymmetricPremonoidal extends caps.Pure { this: Premonoidal =>
  import category.{Iso, Obj, -->, <->, >>>}

  /** The braiding *σ*: *A* ⊗ *B* → *B* ⊗ *A*.
    *
    * @note The braiding is its own inverse. See [[braiding]].
    */
  def braid[A: Obj, B: Obj]: (A * B) --> (B * A)

  private given IIsObj: (I is Obj)                                = unit.evidence
  private given TensorIsObj: [A: Obj, B: Obj] => ((A * B) is Obj) = tensor.objects[A, B]

  /** The braiding isomorphism *σ*: *A* ⊗ *B* ≅ *B* ⊗ *A*. */
  final def braiding[A: Obj, B: Obj]: (A * B) <-> (B * A) = {
    Iso(braid[A, B], braid[B, A])
  }

  /** *ρ* = *λ* ∘ *σ* and *ρ*⁻¹ = *σ* ∘ *λ*⁻¹
    */
  def rightUnitor[A: Obj]: (A * I) <-> A = {
    Iso(braid[A, I] >>> leftUnitor[A].to, leftUnitor[A].from >>> braid[I, A])
  }

  /** Laws that any `SymmetricPremonoidal` structure must satisfy. */
  object SymmetricPremonoidalLaws {
    import PremonoidalLaws.{interchangeLeft, interchangeRight}

    /** *σ* ∘ (*f* ⦸ *C*) = (*C* ⊘ *f*) ∘ *σ*
      */
    def braidLeftNaturality[A: Obj, B: Obj, C: Obj](f: A --> B)(
      using ((A * C) --> (C * B)) is Observable
    ): Boolean = {
      (lmap[A, B, C](f) >>> braid[B, C]) =?= (braid[A, C] >>> rmap[A, B, C](f))
    }

    /** *σ* ∘ (*C* ⊘ *f*) = (*f* ⦸ *C*) ∘ *σ*
      */
    def braidRightNaturality[A: Obj, B: Obj, C: Obj](f: A --> B)(
      using ((C * A) --> (B * C)) is Observable
    ): Boolean = {
      (rmap[A, B, C](f) >>> braid[C, B]) =?= (braid[C, A] >>> lmap[A, B, C](f))
    }

    /** ((*B* ⊗ *A*) ⊘ *g*) ∘ (*σ* ⦸ *X*) = (*σ* ⦸ *Y*) ∘ ((*A* ⊗ *B*) ⊘ *g*), and likewise on the right: *σ* is
      * central.
      */
    def braidCentrality[A: Obj, B: Obj, X: Obj, Y: Obj](g: X --> Y)(
      using
      (((A * B) * X) --> ((B * A) * Y)) is Observable,
      ((X * (A * B)) --> (Y * (B * A))) is Observable,
    ): Boolean = {
      interchangeLeft(braid[A, B], g) && interchangeRight(braid[A, B], g)
    }

    /** *ρ* = *λ* ∘ *σ* and *ρ*⁻¹ = *σ* ∘ *λ*⁻¹
      */
    def rightUnitorIsBraidedLeftUnitor[A: Obj](
      using
      ((A * I) --> A) is Observable,
      (A --> (A * I)) is Observable,
    ): Boolean = {
      (rightUnitor[A].to =?= (braid[A, I] >>> leftUnitor[A].to)) &&
      (rightUnitor[A].from =?= (leftUnitor[A].from >>> braid[I, A]))
    }

    /** *σ* ∘ *σ* = *id*
      */
    def involution[A: Obj, B: Obj](using ((A * B) --> (A * B)) is Observable): Boolean = {
      (braid[A, B] >>> braid[B, A]) =?= category.identity[A * B]
    }

    /** *α* ∘ *σ* ∘ *α* = (*B* ⊘ *σ*) ∘ *α* ∘ (*σ* ⦸ *C*)
      */
    def hexagon[A: Obj, B: Obj, C: Obj](using (((A * B) * C) --> (B * (C * A))) is Observable): Boolean = {
      val lhs = associator[A, B, C].to >>> braid[A, B * C] >>> associator[B, C, A].to
      val rhs = lmap[A * B, B * A, C](braid[A, B]) >>> associator[B, A, C].to >>> rmap[A * C, C * A, B](braid[A, C])
      lhs =?= rhs
    }
  }
}

object SymmetricPremonoidal {

  /** The symmetric premonoidal structures on a category **C**. */
  type On[C <: Category] = Premonoidal.On[C] & SymmetricPremonoidal
}
