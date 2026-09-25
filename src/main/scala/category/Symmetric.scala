package parrot
package category

/** A symmetric monoidal profunctor on an underlying category **C**.
  *
  * Represents a symmetric monoidal profunctor *P* on **C**, where
  *   - *β*: *A* ⊗ *B* ⇒ *B* ⊗ *A* is the braiding
  */
trait Symmetric extends Monoidal {
  type Self[_, _]

  /** The braiding natural isomorphism *β*: *A* ⊗ *B* ~> *B* ⊗ *A*. */
  def braid[A, B]: (A * B) ~> (B * A)

  /** The inverse braiding natural isomorphism *β*⁻¹: *B* ⊗ *A* ~> *A* ⊗ *B*. */
  def braidInv[A, B]: (B * A) ~> (A * B) = {
    braid[B, A]
  }

  /** The right unitor morphism *ρ*: *A* ⊗ *I* ~> *A* = *λ* ∘ *β*. */
  override def rightUnitor[A]: (A * I) ~> A = {
    braid >>> leftUnitor
  }

  /** The inverse right unitor morphism *ρ*⁻¹: *A* ~> *A* ⊗ *I* = *β* ∘ *λ*⁻¹. */
  override def rightUnitorInv[A]: A ~> (A * I) = {
    leftUnitorInv >>> braid
  }

  /** The inverse associator morphism *α*⁻¹: *A* ⊗ (*B* ⊗ *C*) ~> (*A* ⊗ *B*) ⊗ *C* via iterated braiding and
    * association.
    */
  override def unassociate[A, B, C]: (A * (B * C)) ~> ((A * B) * C) = {
    braid >>> associate >>> braid >>> associate >>> braid
  }

  /** Laws that any `Symmetric` monoidal profunctor must satisfy. */
  object SymmetricLaws {

    /** (*g* ⊗ *f*) ∘ *β* = *β* ∘ (*f* ⊗ *g*)
      */
    def braidNaturality[A1, A2, B1, B2](
      f: A1 ~> A2,
      g: B1 ~> B2,
    )(using (A1 * B1) ~> (B2 * A2) is Eq): Boolean = {
      (braid[A1, B1] >>> (g *** f)) === ((f *** g) >>> braid[A2, B2])
    }

    /** *β* ∘ *β* = *id*
      */
    def symmetry[A, B](using (A * B) ~> (A * B) is Eq): Boolean = {
      (braid[A, B] >>> braid[B, A]) === identity[A * B]
    }

    /** *α* ∘ *β* ∘ *α* = (*id* ⊗ *β*) ∘ *α* ∘ (*β* ⊗ *id*)
      */
    def hexagon[A, B, C](using ((A * B) * C) ~> (B * (C * A)) is Eq): Boolean = {
      val lhs = associate[A, B, C] >>> braid[A, B * C] >>> associate[B, C, A]
      val rhs = (braid[A, B] *** identity[C]) >>> associate[B, A, C] >>> (identity[B] *** braid[A, C])
      lhs === rhs
    }
  }
}

object Symmetric {

  /** Type helper to refine `I` and `Tensor` simultaneously on `Symmetric`. */
  type `with`[U, T[_, _]] = Symmetric { type I = U; type Tensor = T }

  /** Summons the `Symmetric` instance of `P`. */
  def apply[P[_, _]: Symmetric]: P is Symmetric = summon

  /** `Symmetric` instance for `Function` on the category **Type**. */
  given FunctionIsSymmetric
    : (P: Function is Monoidal.`with`[Unit, [A, B] =>> (A, B)] on Function)
        => Function is Symmetric {
    export P.{
      Self as _,
      rightUnitor as _,
      rightUnitorInv as _,
      unassociate as _,
      *,
    }

    def braid[A, B]: ((A, B)) => (B, A) = {
      (a, b) => (b, a)
    }
  }
}
